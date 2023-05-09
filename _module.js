function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert(target, node, anchor) {
    target.insertBefore(node, anchor || null);
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function find_comment(nodes, text, start) {
    for (let i = start; i < nodes.length; i += 1) {
        const node = nodes[i];
        if (node.nodeType === 8 /* comment node */ && node.textContent.trim() === text) {
            return i;
        }
    }
    return nodes.length;
}
function claim_html_tag(nodes, is_svg) {
    // find html opening tag
    const start_index = find_comment(nodes, 'HTML_TAG_START', 0);
    const end_index = find_comment(nodes, 'HTML_TAG_END', start_index);
    if (start_index === end_index) {
        return new HtmlTagHydration(undefined, is_svg);
    }
    init_claim_info(nodes);
    const html_tag_nodes = nodes.splice(start_index, end_index - start_index + 1);
    detach(html_tag_nodes[0]);
    detach(html_tag_nodes[html_tag_nodes.length - 1]);
    const claimed_nodes = html_tag_nodes.slice(1, html_tag_nodes.length - 1);
    for (const n of claimed_nodes) {
        n.claim_order = nodes.claim_info.total_claimed;
        nodes.claim_info.total_claimed += 1;
    }
    return new HtmlTagHydration(claimed_nodes, is_svg);
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}
class HtmlTag {
    constructor(is_svg = false) {
        this.is_svg = false;
        this.is_svg = is_svg;
        this.e = this.n = null;
    }
    c(html) {
        this.h(html);
    }
    m(html, target, anchor = null) {
        if (!this.e) {
            if (this.is_svg)
                this.e = svg_element(target.nodeName);
            /** #7364  target for <template> may be provided as #document-fragment(11) */
            else
                this.e = element((target.nodeType === 11 ? 'TEMPLATE' : target.nodeName));
            this.t = target.tagName !== 'TEMPLATE' ? target : target.content;
            this.c(html);
        }
        this.i(anchor);
    }
    h(html) {
        this.e.innerHTML = html;
        this.n = Array.from(this.e.nodeName === 'TEMPLATE' ? this.e.content.childNodes : this.e.childNodes);
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert(this.t, this.n[i], anchor);
        }
    }
    p(html) {
        this.d();
        this.h(html);
        this.i(this.a);
    }
    d() {
        this.n.forEach(detach);
    }
}
class HtmlTagHydration extends HtmlTag {
    constructor(claimed_nodes, is_svg = false) {
        super(is_svg);
        this.e = this.n = null;
        this.l = claimed_nodes;
    }
    c(html) {
        if (this.l) {
            this.n = this.l;
        }
        else {
            super.c(html);
        }
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert_hydration(this.t, this.n[i], anchor);
        }
    }
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link;
	let link_href_value;
	let title_value;
	let meta2;
	let script;
	let script_src_value;
	let style;
	let t;
	document.title = title_value = /*title*/ ctx[0];

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link = element("link");
			meta2 = element("meta");
			script = element("script");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/tailwindcss@2.2.15/dist/base.css\");\n@import url(https://fonts.bunny.net/css?family=archivo:200,300,300i,400,400i,500,500i,600,600i,700,700i);\n\n#page {\n  --color-primored: #35d994;\n  --color-gray: #262626;\n  --color-black: #121212;\n  --color-white: #ffff;\n  --color-accent: var(--color-primored);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.1);\n\n  --padding-left: 2rem;\n  --padding-right: 2rem;\n\n  --color: #F3F3F3;\n  --background: var(--color-black);\n  --max-width: 1000px;\n  --border-color: var(--color-gray);\n  --border: 2px solid var(--border-color);\n  --border-radius: 5px;\n\n  --heading-font-size: 2.25rem;\n  --heading-color: #FDFDFD;\n  --heading-font-weight: 600;\n  --subheading-color: #DADADA;\n  --body-color: #CECECE;\n\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color, var(--transition-time) background,\n    var(--transition-time) border-color,\n    var(--transition-time) text-decoration-color,\n    var(--transition-time) box-shadow, var(--transition-time) transform;\n\n  --button-color: var(--body-color);\n  --button-background: var(--background);\n  --button-border: 1px solid white;\n  --button-hover-background: var(--color-primored);\n  --button-padding: 8px 20px;\n  --button-border-radius: 5px;\n\n  --padding: 2rem;\n\n  color: var(--body-color);\n  background: var(--background);\n  font-family: \"Inter\", system-ui, sans-serif;\n  transition: var(--transition);\n}\n\n#page[lang=\"ar\"] {\n    direction: rtl;\n  }\n\n#page{\n  font-weight: 300;\n}\n\n.section-container {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding-left: var(--padding);\n  padding-right: var(--padding);\n  padding-top: 5rem;\n  padding-bottom: 5rem;\n}\n\n.button {\n  display: flex;\n  align-items: center;\n  gap: 0.25rem;\n  color: var(--button-color);\n  border: var(--button-border);\n  border-radius: 6px;\n  padding: var(--button-padding);\n  transition: var(--transition);\n  transform: translateY(0);\n}\n\n.button.secondary {\n    border: 0;\n    color: var(--color-white);\n    background: var(--color-gray);\n  }\n\n.button.is-primary {\n    border: 1.5px solid var(--color-accent);\n  }\n\n.button.small {\n    color: var(--color);\n    padding: 0.25rem 0.75rem 0.25rem 0.25rem;\n    font-size: 0.75rem;\n    background: transparent;\n    border: 1.5px solid var(--border-color);\n    display: flex;\n    margin-bottom: 1rem;\n  }\n\n.button.small svg {\n      width: 1rem;\n      height: 1rem;\n    }\n\n.button:hover {\n    border-color: transparent;\n    background: var(--color-background);\n    color: white;\n    box-shadow: 0 0 0 2px var(--color-accent);\n  }\n\n.button.disabled {\n    cursor: disabled;\n    opacity: 0.5;\n    pointer-events: none;\n  }\n\n.heading {\n  font-family: \"Archivo\", system-ui, sans-serif;\n  font-size: var(--heading-font-size, 49px);\n  line-height: var(--heading-line-height, 1.15);\n  font-weight: var(--heading-font-weight, 500);\n  color: var(--heading-color, #252428);\n  text-align: center;\n  text-wrap: balance;\n}\n\nh2.heading {\n  line-height: 1.15;\n  font-size: 2.5rem;\n}\n\n.subheading {\n  text-align: center;\n  font-size: 1.125rem;\n}\n\n.link {\n  transition: border-color 0.1s;\n}\n\n.link:hover {\n    border-color: transparent;\n  }\n\n.link.underlined {\n    border-bottom: 2px solid var(--color-accent, #154bf4);\n  }\n\n.link.underlined:hover {\n      border-color: transparent;\n    }\n\n.link.arrow {\n    display: inline-flex;\n    align-items: center;\n    color: var(--color-accent);\n    font-weight: 500;\n  }\n\n.link.arrow svg {\n      transition: 0.1s transform;\n      transform: translateX(0);\n      position: relative;\n      top: 2px;\n    }\n\n.link.arrow span {\n      margin-right: 0.5rem;\n    }\n\n.link.arrow:hover svg {\n      transform: translateX(4px);\n    }\n\n.content {\n  margin: 0 auto;\n  padding: 4rem var(--padding);\n}\n\n.content blockquote {\n    padding: 2rem;\n    border-left: 5px solid var(--border-color);\n    margin: 2rem 0;\n    font-size: 1.5rem;\n  }\n\n.content h1 {\n    font-family: \"Archivo\", system-ui, sans-serif;\n    color: var(--color);\n    font-size: 2.5rem;\n    font-weight: 600;\n    margin-bottom: 1rem;\n    font-weight: 700;\n    letter-spacing: -0.01em;\n  }\n\n.content h2 {\n    font-family: \"Archivo\", system-ui, sans-serif;\n    color: var(--color);\n    font-size: 2.25rem;\n    font-weight: 600;\n    line-height: 1.3;\n    margin-top: 3rem;\n    margin-bottom: 1rem;\n  }\n\n.content h2 + h3 {\n    margin-top: 0;\n  }\n\n.content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    padding-bottom: .5rem;\n    margin-top: 2rem;\n  }\n\n.content h4 {\n    font-size: 1.25rem;\n    font-weight: 600;\n    line-height: 1;\n    margin-bottom: .5rem;\n  }\n\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n  }\n\n.content p {\n    line-height: 1.6;\n    font-size: 1.125rem;\n    font-weight: 300;\n  }\n\n.content p:not(:last-child) {\n      margin-bottom: 1rem;\n    }\n\n.content ol {\n    list-style: decimal;\n    padding-left: 1.25rem;\n  }\n\n.content ul {\n    list-style: disc;\n    padding-left: 1.25rem;\n    margin-bottom: 1rem;\n  }\n\n.content ul li {\n      padding: 0.25rem 0;\n    }\n\n.content strong {\n    font-weight: 500;\n    color: #35\n  }\n\n.content hr {\n    border-color: var(--border-color); \n    margin-block: 5rem; \n  }\n\n.content a {\n    border-bottom: 2px solid var(--color-accent);\n  }\n\nform {\n  display: grid;\n  gap: 1rem;\n}\n\nform label {\n    display: grid;\n    gap: 0.25rem;\n  }\n\nform label span {\n      font-size: 0.75rem;\n      font-weight: 500;\n    }\n\nform label input,\n    form label textarea {\n      padding: 0.5rem;\n      outline-color: transparent;\n      color: #222;\n      transition: var(--transition, 0.1s outline-color);\n      border: 1.5px solid var(--border-color, #eee);\n      border-radius: var(--border-radius);\n    }\n\nform label input:focus, form label textarea:focus {\n        outline-color: var(--color-accent, rebeccapurple);\n      }\n\nform label input::-moz-placeholder, form label textarea::-moz-placeholder {\n        font-weight: 300;\n      }\n\nform label input:-ms-input-placeholder, form label textarea:-ms-input-placeholder {\n        font-weight: 300;\n      }\n\nform label input::placeholder, form label textarea::placeholder {\n        font-weight: 300;\n      }\n\nform .button {\n    margin-top: 0.5rem;\n    display: flex;\n    justify-content: center; \n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1ou479e', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link = claim_element(head_nodes, "LINK", { rel: true, type: true, href: true });
			meta2 = claim_element(head_nodes, "META", { name: true, content: true });
			script = claim_element(head_nodes, "SCRIPT", { "data-domain": true, src: true });
			var script_nodes = children(script);
			script_nodes.forEach(detach);
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/tailwindcss@2.2.15/dist/base.css\");\n@import url(https://fonts.bunny.net/css?family=archivo:200,300,300i,400,400i,500,500i,600,600i,700,700i);\n\n#page {\n  --color-primored: #35d994;\n  --color-gray: #262626;\n  --color-black: #121212;\n  --color-white: #ffff;\n  --color-accent: var(--color-primored);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.1);\n\n  --padding-left: 2rem;\n  --padding-right: 2rem;\n\n  --color: #F3F3F3;\n  --background: var(--color-black);\n  --max-width: 1000px;\n  --border-color: var(--color-gray);\n  --border: 2px solid var(--border-color);\n  --border-radius: 5px;\n\n  --heading-font-size: 2.25rem;\n  --heading-color: #FDFDFD;\n  --heading-font-weight: 600;\n  --subheading-color: #DADADA;\n  --body-color: #CECECE;\n\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color, var(--transition-time) background,\n    var(--transition-time) border-color,\n    var(--transition-time) text-decoration-color,\n    var(--transition-time) box-shadow, var(--transition-time) transform;\n\n  --button-color: var(--body-color);\n  --button-background: var(--background);\n  --button-border: 1px solid white;\n  --button-hover-background: var(--color-primored);\n  --button-padding: 8px 20px;\n  --button-border-radius: 5px;\n\n  --padding: 2rem;\n\n  color: var(--body-color);\n  background: var(--background);\n  font-family: \"Inter\", system-ui, sans-serif;\n  transition: var(--transition);\n}\n\n#page[lang=\"ar\"] {\n    direction: rtl;\n  }\n\n#page{\n  font-weight: 300;\n}\n\n.section-container {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding-left: var(--padding);\n  padding-right: var(--padding);\n  padding-top: 5rem;\n  padding-bottom: 5rem;\n}\n\n.button {\n  display: flex;\n  align-items: center;\n  gap: 0.25rem;\n  color: var(--button-color);\n  border: var(--button-border);\n  border-radius: 6px;\n  padding: var(--button-padding);\n  transition: var(--transition);\n  transform: translateY(0);\n}\n\n.button.secondary {\n    border: 0;\n    color: var(--color-white);\n    background: var(--color-gray);\n  }\n\n.button.is-primary {\n    border: 1.5px solid var(--color-accent);\n  }\n\n.button.small {\n    color: var(--color);\n    padding: 0.25rem 0.75rem 0.25rem 0.25rem;\n    font-size: 0.75rem;\n    background: transparent;\n    border: 1.5px solid var(--border-color);\n    display: flex;\n    margin-bottom: 1rem;\n  }\n\n.button.small svg {\n      width: 1rem;\n      height: 1rem;\n    }\n\n.button:hover {\n    border-color: transparent;\n    background: var(--color-background);\n    color: white;\n    box-shadow: 0 0 0 2px var(--color-accent);\n  }\n\n.button.disabled {\n    cursor: disabled;\n    opacity: 0.5;\n    pointer-events: none;\n  }\n\n.heading {\n  font-family: \"Archivo\", system-ui, sans-serif;\n  font-size: var(--heading-font-size, 49px);\n  line-height: var(--heading-line-height, 1.15);\n  font-weight: var(--heading-font-weight, 500);\n  color: var(--heading-color, #252428);\n  text-align: center;\n  text-wrap: balance;\n}\n\nh2.heading {\n  line-height: 1.15;\n  font-size: 2.5rem;\n}\n\n.subheading {\n  text-align: center;\n  font-size: 1.125rem;\n}\n\n.link {\n  transition: border-color 0.1s;\n}\n\n.link:hover {\n    border-color: transparent;\n  }\n\n.link.underlined {\n    border-bottom: 2px solid var(--color-accent, #154bf4);\n  }\n\n.link.underlined:hover {\n      border-color: transparent;\n    }\n\n.link.arrow {\n    display: inline-flex;\n    align-items: center;\n    color: var(--color-accent);\n    font-weight: 500;\n  }\n\n.link.arrow svg {\n      transition: 0.1s transform;\n      transform: translateX(0);\n      position: relative;\n      top: 2px;\n    }\n\n.link.arrow span {\n      margin-right: 0.5rem;\n    }\n\n.link.arrow:hover svg {\n      transform: translateX(4px);\n    }\n\n.content {\n  margin: 0 auto;\n  padding: 4rem var(--padding);\n}\n\n.content blockquote {\n    padding: 2rem;\n    border-left: 5px solid var(--border-color);\n    margin: 2rem 0;\n    font-size: 1.5rem;\n  }\n\n.content h1 {\n    font-family: \"Archivo\", system-ui, sans-serif;\n    color: var(--color);\n    font-size: 2.5rem;\n    font-weight: 600;\n    margin-bottom: 1rem;\n    font-weight: 700;\n    letter-spacing: -0.01em;\n  }\n\n.content h2 {\n    font-family: \"Archivo\", system-ui, sans-serif;\n    color: var(--color);\n    font-size: 2.25rem;\n    font-weight: 600;\n    line-height: 1.3;\n    margin-top: 3rem;\n    margin-bottom: 1rem;\n  }\n\n.content h2 + h3 {\n    margin-top: 0;\n  }\n\n.content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    padding-bottom: .5rem;\n    margin-top: 2rem;\n  }\n\n.content h4 {\n    font-size: 1.25rem;\n    font-weight: 600;\n    line-height: 1;\n    margin-bottom: .5rem;\n  }\n\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n  }\n\n.content p {\n    line-height: 1.6;\n    font-size: 1.125rem;\n    font-weight: 300;\n  }\n\n.content p:not(:last-child) {\n      margin-bottom: 1rem;\n    }\n\n.content ol {\n    list-style: decimal;\n    padding-left: 1.25rem;\n  }\n\n.content ul {\n    list-style: disc;\n    padding-left: 1.25rem;\n    margin-bottom: 1rem;\n  }\n\n.content ul li {\n      padding: 0.25rem 0;\n    }\n\n.content strong {\n    font-weight: 500;\n    color: #35\n  }\n\n.content hr {\n    border-color: var(--border-color); \n    margin-block: 5rem; \n  }\n\n.content a {\n    border-bottom: 2px solid var(--color-accent);\n  }\n\nform {\n  display: grid;\n  gap: 1rem;\n}\n\nform label {\n    display: grid;\n    gap: 0.25rem;\n  }\n\nform label span {\n      font-size: 0.75rem;\n      font-weight: 500;\n    }\n\nform label input,\n    form label textarea {\n      padding: 0.5rem;\n      outline-color: transparent;\n      color: #222;\n      transition: var(--transition, 0.1s outline-color);\n      border: 1.5px solid var(--border-color, #eee);\n      border-radius: var(--border-radius);\n    }\n\nform label input:focus, form label textarea:focus {\n        outline-color: var(--color-accent, rebeccapurple);\n      }\n\nform label input::-moz-placeholder, form label textarea::-moz-placeholder {\n        font-weight: 300;\n      }\n\nform label input:-ms-input-placeholder, form label textarea:-ms-input-placeholder {\n        font-weight: 300;\n      }\n\nform label input::placeholder, form label textarea::placeholder {\n        font-weight: 300;\n      }\n\nform .button {\n    margin-top: 0.5rem;\n    display: flex;\n    justify-content: center; \n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link, "rel", "shortcut icon");
			attr(link, "type", "image/jpg");
			attr(link, "href", link_href_value = /*favicon*/ ctx[1].url);
			attr(meta2, "name", "description");
			attr(meta2, "content", /*description*/ ctx[2]);
			script.defer = true;
			attr(script, "data-domain", "primocms.org");
			if (!src_url_equal(script.src, script_src_value = "https://plausible.io/js/script.js")) attr(script, "src", script_src_value);
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link);
			append_hydration(document.head, meta2);
			append_hydration(document.head, script);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 2 && link_href_value !== (link_href_value = /*favicon*/ ctx[1].url)) {
				attr(link, "href", link_href_value);
			}

			if (dirty & /*title*/ 1 && title_value !== (title_value = /*title*/ ctx[0])) {
				document.title = title_value;
			}

			if (dirty & /*description*/ 4) {
				attr(meta2, "content", /*description*/ ctx[2]);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link);
			detach(meta2);
			detach(script);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(1, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
	};

	return [title, favicon, description];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { title: 0, favicon: 1, description: 2 });
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	child_ctx[9] = list[i].links;
	const constants_0 = /*links*/ child_ctx[9].length > 0;
	child_ctx[10] = constants_0;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	child_ctx[9] = list[i].links;
	child_ctx[15] = list[i].featured;
	const constants_0 = /*links*/ child_ctx[9].length > 0;
	child_ctx[10] = constants_0;
	return child_ctx;
}

function get_each_context_3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (245:14) {#if banner.label}
function create_if_block_5(ctx) {
	let div1;
	let div0;
	let p;
	let raw_value = /*banner*/ ctx[0].label + "";
	let t;
	let if_block = /*banner*/ ctx[0].cta.label && create_if_block_6(ctx);

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			p = element("p");
			t = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			p = claim_element(div0_nodes, "P", {});
			var p_nodes = children(p);
			p_nodes.forEach(detach);
			t = claim_space(div0_nodes);
			if (if_block) if_block.l(div0_nodes);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "memo-content svelte-d3ch18");
			attr(div1, "class", "banner svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, p);
			p.innerHTML = raw_value;
			append_hydration(div0, t);
			if (if_block) if_block.m(div0, null);
		},
		p(ctx, dirty) {
			if (dirty & /*banner*/ 1 && raw_value !== (raw_value = /*banner*/ ctx[0].label + "")) p.innerHTML = raw_value;
			if (/*banner*/ ctx[0].cta.label) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_6(ctx);
					if_block.c();
					if_block.m(div0, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		d(detaching) {
			if (detaching) detach(div1);
			if (if_block) if_block.d();
		}
	};
}

// (249:6) {#if banner.cta.label}
function create_if_block_6(ctx) {
	let a;
	let t_value = /*banner*/ ctx[0].cta.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*banner*/ ctx[0].cta.url);
			attr(a, "class", "svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*banner*/ 1 && t_value !== (t_value = /*banner*/ ctx[0].cta.label + "")) set_data(t, t_value);

			if (dirty & /*banner*/ 1 && a_href_value !== (a_href_value = /*banner*/ ctx[0].cta.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (272:10) {#if featured}
function create_if_block_4(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text("New");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "New");
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "featured-pill svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (278:10) {:else}
function create_else_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "class", "link svelte-d3ch18");
			toggle_class(a, "active", /*link*/ ctx[8].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*nav, window*/ 4) {
				toggle_class(a, "active", /*link*/ ctx[8].url === window.location.pathname);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (275:10) {#if hasDropdown}
function create_if_block_3(ctx) {
	let span0;
	let t0_value = /*link*/ ctx[8].label + "";
	let t0;
	let t1;
	let span1;
	let icon;
	let current;

	icon = new Component$1({
			props: { icon: "akar-icons:chevron-down" }
		});

	return {
		c() {
			span0 = element("span");
			t0 = text(t0_value);
			t1 = space();
			span1 = element("span");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			span0 = claim_element(nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			span0_nodes.forEach(detach);
			t1 = claim_space(nodes);
			span1 = claim_element(nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			claim_component(icon.$$.fragment, span1_nodes);
			span1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "svelte-d3ch18");
			attr(span1, "class", "icon svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, span0, anchor);
			append_hydration(span0, t0);
			insert_hydration(target, t1, anchor);
			insert_hydration(target, span1, anchor);
			mount_component(icon, span1, null);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*nav*/ 4) && t0_value !== (t0_value = /*link*/ ctx[8].label + "")) set_data(t0, t0_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(span0);
			if (detaching) detach(t1);
			if (detaching) detach(span1);
			destroy_component(icon);
		}
	};
}

// (285:8) {#if hasDropdown}
function create_if_block_2(ctx) {
	let div;
	let each_value_3 = /*links*/ ctx[9];
	let each_blocks = [];

	for (let i = 0; i < each_value_3.length; i += 1) {
		each_blocks[i] = create_each_block_3(get_each_context_3(ctx, each_value_3, i));
	}

	return {
		c() {
			div = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div_nodes);
			}

			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "dropdown svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div, null);
				}
			}
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4) {
				each_value_3 = /*links*/ ctx[9];
				let i;

				for (i = 0; i < each_value_3.length; i += 1) {
					const child_ctx = get_each_context_3(ctx, each_value_3, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_3(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_3.length;
			}
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

// (287:12) {#each links as { link }}
function create_each_block_3(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "class", "link svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (268:4) {#each nav as { link, links, featured }}
function create_each_block_2(ctx) {
	let div1;
	let div0;
	let t0;
	let current_block_type_index;
	let if_block1;
	let t1;
	let current;
	let if_block0 = /*featured*/ ctx[15] && create_if_block_4();
	const if_block_creators = [create_if_block_3, create_else_block_1];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*hasDropdown*/ ctx[10]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type(ctx);
	if_block1 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	let if_block2 = /*hasDropdown*/ ctx[10] && create_if_block_2(ctx);

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			if (if_block0) if_block0.c();
			t0 = space();
			if_block1.c();
			t1 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			if (if_block0) if_block0.l(div0_nodes);
			t0 = claim_space(div0_nodes);
			if_block1.l(div0_nodes);
			div0_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "top-link svelte-d3ch18");
			attr(div1, "class", "nav-item svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			if (if_block0) if_block0.m(div0, null);
			append_hydration(div0, t0);
			if_blocks[current_block_type_index].m(div0, null);
			append_hydration(div1, t1);
			if (if_block2) if_block2.m(div1, null);
			current = true;
		},
		p(ctx, dirty) {
			if (/*featured*/ ctx[15]) {
				if (if_block0) ; else {
					if_block0 = create_if_block_4();
					if_block0.c();
					if_block0.m(div0, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block1 = if_blocks[current_block_type_index];

				if (!if_block1) {
					if_block1 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block1.c();
				} else {
					if_block1.p(ctx, dirty);
				}

				transition_in(if_block1, 1);
				if_block1.m(div0, null);
			}

			if (/*hasDropdown*/ ctx[10]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);
				} else {
					if_block2 = create_if_block_2(ctx);
					if_block2.c();
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				if_block2.d(1);
				if_block2 = null;
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			if (if_block0) if_block0.d();
			if_blocks[current_block_type_index].d();
			if (if_block2) if_block2.d();
		}
	};
}

// (298:2) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav_1;
	let t;
	let button;
	let icon;
	let nav_1_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*nav*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { icon: "bi:x-lg" } });

	return {
		c() {
			nav_1 = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav_1 = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_1_nodes = children(nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			t = claim_space(nav_1_nodes);

			button = claim_element(nav_1_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-d3ch18");
			attr(nav_1, "id", "mobile-nav");
			attr(nav_1, "class", "svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, nav_1, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav_1, null);
				}
			}

			append_hydration(nav_1, t);
			append_hydration(nav_1, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*toggleMobileNav*/ ctx[4]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4) {
				each_value = /*nav*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav_1, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_1_transition) nav_1_transition = create_bidirectional_transition(nav_1, fade, { duration: 200 }, true);
				nav_1_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_1_transition) nav_1_transition = create_bidirectional_transition(nav_1, fade, { duration: 200 }, false);
			nav_1_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav_1);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_1_transition) nav_1_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (306:8) {:else}
function create_else_block$1(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "class", "link svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (302:8) {#if hasDropdown}
function create_if_block_1$1(ctx) {
	let each_1_anchor;
	let each_value_1 = /*links*/ ctx[9];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	return {
		c() {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			each_1_anchor = empty();
		},
		l(nodes) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nodes);
			}

			each_1_anchor = empty();
		},
		m(target, anchor) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(target, anchor);
				}
			}

			insert_hydration(target, each_1_anchor, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4) {
				each_value_1 = /*links*/ ctx[9];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(each_1_anchor.parentNode, each_1_anchor);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		d(detaching) {
			destroy_each(each_blocks, detaching);
			if (detaching) detach(each_1_anchor);
		}
	};
}

// (303:10) {#each links as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "class", "link svelte-d3ch18");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (300:6) {#each nav as { link, links }}
function create_each_block(ctx) {
	let if_block_anchor;

	function select_block_type_1(ctx, dirty) {
		if (/*hasDropdown*/ ctx[10]) return create_if_block_1$1;
		return create_else_block$1;
	}

	let current_block_type = select_block_type_1(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type_1(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let div1;
	let t0;
	let header;
	let a0;
	let span0;
	let t1_value = /*logo*/ ctx[1].title + "";
	let t1;
	let t2;
	let html_tag;
	let raw_value = /*logo*/ ctx[1].svg + "";
	let t3;
	let nav_1;
	let a1;
	let icon0;
	let t4;
	let span1;
	let t5;
	let t6;
	let t7;
	let button;
	let div0;
	let icon1;
	let t8;
	let current;
	let mounted;
	let dispose;
	let if_block0 = /*banner*/ ctx[0].label && create_if_block_5(ctx);

	icon0 = new Component$1({
			props: { icon: "ic:outline-star-purple500" }
		});

	let each_value_2 = /*nav*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	icon1 = new Component$1({ props: { icon: "eva:menu-outline" } });
	let if_block1 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			if (if_block0) if_block0.c();
			t0 = space();
			header = element("header");
			a0 = element("a");
			span0 = element("span");
			t1 = text(t1_value);
			t2 = space();
			html_tag = new HtmlTagHydration(false);
			t3 = space();
			nav_1 = element("nav");
			a1 = element("a");
			create_component(icon0.$$.fragment);
			t4 = space();
			span1 = element("span");
			t5 = text("Star on Github");
			t6 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t7 = space();
			button = element("button");
			div0 = element("div");
			create_component(icon1.$$.fragment);
			t8 = space();
			if (if_block1) if_block1.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			if (if_block0) if_block0.l(div1_nodes);
			t0 = claim_space(div1_nodes);
			header = claim_element(div1_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			a0 = claim_element(header_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			span0 = claim_element(a0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t1 = claim_text(span0_nodes, t1_value);
			span0_nodes.forEach(detach);
			t2 = claim_space(a0_nodes);
			html_tag = claim_html_tag(a0_nodes, false);
			a0_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			nav_1 = claim_element(header_nodes, "NAV", { class: true });
			var nav_1_nodes = children(nav_1);

			a1 = claim_element(nav_1_nodes, "A", {
				class: true,
				href: true,
				"aria-label": true
			});

			var a1_nodes = children(a1);
			claim_component(icon0.$$.fragment, a1_nodes);
			t4 = claim_space(a1_nodes);
			span1 = claim_element(a1_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t5 = claim_text(span1_nodes, "Star on Github");
			span1_nodes.forEach(detach);
			a1_nodes.forEach(detach);
			t6 = claim_space(nav_1_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			t7 = claim_space(nav_1_nodes);
			button = claim_element(nav_1_nodes, "BUTTON", { id: true, class: true });
			var button_nodes = children(button);
			div0 = claim_element(button_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			claim_component(icon1.$$.fragment, div0_nodes);
			div0_nodes.forEach(detach);
			button_nodes.forEach(detach);
			nav_1_nodes.forEach(detach);
			t8 = claim_space(header_nodes);
			if (if_block1) if_block1.l(header_nodes);
			header_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "svelte-d3ch18");
			html_tag.a = null;
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-d3ch18");
			attr(span1, "class", "svelte-d3ch18");
			attr(a1, "class", "link pill svelte-d3ch18");
			attr(a1, "href", "https://github.com/primocms/primo");
			attr(a1, "aria-label", "Github repo");
			attr(div0, "class", "menu-icon svelte-d3ch18");
			attr(button, "id", "open");
			attr(button, "class", "svelte-d3ch18");
			attr(nav_1, "class", "svelte-d3ch18");
			attr(header, "class", "section-container svelte-d3ch18");
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-caf0af11-e039-41a5-a9b8-242e7785befc");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			if (if_block0) if_block0.m(div1, null);
			append_hydration(div1, t0);
			append_hydration(div1, header);
			append_hydration(header, a0);
			append_hydration(a0, span0);
			append_hydration(span0, t1);
			append_hydration(a0, t2);
			html_tag.m(raw_value, a0);
			append_hydration(header, t3);
			append_hydration(header, nav_1);
			append_hydration(nav_1, a1);
			mount_component(icon0, a1, null);
			append_hydration(a1, t4);
			append_hydration(a1, span1);
			append_hydration(span1, t5);
			append_hydration(nav_1, t6);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav_1, null);
				}
			}

			append_hydration(nav_1, t7);
			append_hydration(nav_1, button);
			append_hydration(button, div0);
			mount_component(icon1, div0, null);
			append_hydration(header, t8);
			if (if_block1) if_block1.m(header, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*toggleMobileNav*/ ctx[4]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (/*banner*/ ctx[0].label) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_5(ctx);
					if_block0.c();
					if_block0.m(div1, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if ((!current || dirty & /*logo*/ 2) && t1_value !== (t1_value = /*logo*/ ctx[1].title + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*logo*/ 2) && raw_value !== (raw_value = /*logo*/ ctx[1].svg + "")) html_tag.p(raw_value);

			if (dirty & /*nav, window*/ 4) {
				each_value_2 = /*nav*/ ctx[2];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_2(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(nav_1, t7);
					}
				}

				group_outros();

				for (i = each_value_2.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block$1(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(header, null);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon0.$$.fragment, local);

			for (let i = 0; i < each_value_2.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			transition_in(icon1.$$.fragment, local);
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(icon0.$$.fragment, local);
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			transition_out(icon1.$$.fragment, local);
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block0) if_block0.d();
			destroy_component(icon0);
			destroy_each(each_blocks, detaching);
			destroy_component(icon1);
			if (if_block1) if_block1.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { banner } = $$props;
	let { logo } = $$props;
	let { nav } = $$props;
	let mobileNavOpen = false;

	function toggleMobileNav() {
		$$invalidate(3, mobileNavOpen = !mobileNavOpen);
	}

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(5, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(6, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(7, description = $$props.description);
		if ('banner' in $$props) $$invalidate(0, banner = $$props.banner);
		if ('logo' in $$props) $$invalidate(1, logo = $$props.logo);
		if ('nav' in $$props) $$invalidate(2, nav = $$props.nav);
	};

	return [banner, logo, nav, mobileNavOpen, toggleMobileNav, title, favicon, description];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			title: 5,
			favicon: 6,
			description: 7,
			banner: 0,
			logo: 1,
			nav: 2
		});
	}
}

var browser = typeof self == "object" ? self.FormData : window.FormData;

var global$1 = typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {};
function bind(fn, thisArg) {
  return function wrap() {
    return fn.apply(thisArg, arguments);
  };
}
const {toString} = Object.prototype;
const {getPrototypeOf} = Object;
const kindOf = ((cache) => (thing) => {
  const str = toString.call(thing);
  return cache[str] || (cache[str] = str.slice(8, -1).toLowerCase());
})(Object.create(null));
const kindOfTest = (type) => {
  type = type.toLowerCase();
  return (thing) => kindOf(thing) === type;
};
const typeOfTest = (type) => (thing) => typeof thing === type;
const {isArray} = Array;
const isUndefined = typeOfTest("undefined");
function isBuffer(val) {
  return val !== null && !isUndefined(val) && val.constructor !== null && !isUndefined(val.constructor) && isFunction(val.constructor.isBuffer) && val.constructor.isBuffer(val);
}
const isArrayBuffer = kindOfTest("ArrayBuffer");
function isArrayBufferView(val) {
  let result;
  if (typeof ArrayBuffer !== "undefined" && ArrayBuffer.isView) {
    result = ArrayBuffer.isView(val);
  } else {
    result = val && val.buffer && isArrayBuffer(val.buffer);
  }
  return result;
}
const isString = typeOfTest("string");
const isFunction = typeOfTest("function");
const isNumber = typeOfTest("number");
const isObject = (thing) => thing !== null && typeof thing === "object";
const isBoolean = (thing) => thing === true || thing === false;
const isPlainObject = (val) => {
  if (kindOf(val) !== "object") {
    return false;
  }
  const prototype2 = getPrototypeOf(val);
  return (prototype2 === null || prototype2 === Object.prototype || Object.getPrototypeOf(prototype2) === null) && !(Symbol.toStringTag in val) && !(Symbol.iterator in val);
};
const isDate = kindOfTest("Date");
const isFile = kindOfTest("File");
const isBlob = kindOfTest("Blob");
const isFileList = kindOfTest("FileList");
const isStream = (val) => isObject(val) && isFunction(val.pipe);
const isFormData = (thing) => {
  const pattern = "[object FormData]";
  return thing && (typeof FormData === "function" && thing instanceof FormData || toString.call(thing) === pattern || isFunction(thing.toString) && thing.toString() === pattern);
};
const isURLSearchParams = kindOfTest("URLSearchParams");
const trim = (str) => str.trim ? str.trim() : str.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g, "");
function forEach(obj, fn, {allOwnKeys = false} = {}) {
  if (obj === null || typeof obj === "undefined") {
    return;
  }
  let i;
  let l;
  if (typeof obj !== "object") {
    obj = [obj];
  }
  if (isArray(obj)) {
    for (i = 0, l = obj.length; i < l; i++) {
      fn.call(null, obj[i], i, obj);
    }
  } else {
    const keys = allOwnKeys ? Object.getOwnPropertyNames(obj) : Object.keys(obj);
    const len = keys.length;
    let key;
    for (i = 0; i < len; i++) {
      key = keys[i];
      fn.call(null, obj[key], key, obj);
    }
  }
}
function findKey(obj, key) {
  key = key.toLowerCase();
  const keys = Object.keys(obj);
  let i = keys.length;
  let _key;
  while (i-- > 0) {
    _key = keys[i];
    if (key === _key.toLowerCase()) {
      return _key;
    }
  }
  return null;
}
const _global = typeof self === "undefined" ? typeof global$1 === "undefined" ? void 0 : global$1 : self;
const isContextDefined = (context) => !isUndefined(context) && context !== _global;
function merge() {
  const {caseless} = isContextDefined(this) && this || {};
  const result = {};
  const assignValue = (val, key) => {
    const targetKey = caseless && findKey(result, key) || key;
    if (isPlainObject(result[targetKey]) && isPlainObject(val)) {
      result[targetKey] = merge(result[targetKey], val);
    } else if (isPlainObject(val)) {
      result[targetKey] = merge({}, val);
    } else if (isArray(val)) {
      result[targetKey] = val.slice();
    } else {
      result[targetKey] = val;
    }
  };
  for (let i = 0, l = arguments.length; i < l; i++) {
    arguments[i] && forEach(arguments[i], assignValue);
  }
  return result;
}
const extend = (a, b, thisArg, {allOwnKeys} = {}) => {
  forEach(b, (val, key) => {
    if (thisArg && isFunction(val)) {
      a[key] = bind(val, thisArg);
    } else {
      a[key] = val;
    }
  }, {allOwnKeys});
  return a;
};
const stripBOM = (content) => {
  if (content.charCodeAt(0) === 65279) {
    content = content.slice(1);
  }
  return content;
};
const inherits = (constructor, superConstructor, props, descriptors2) => {
  constructor.prototype = Object.create(superConstructor.prototype, descriptors2);
  constructor.prototype.constructor = constructor;
  Object.defineProperty(constructor, "super", {
    value: superConstructor.prototype
  });
  props && Object.assign(constructor.prototype, props);
};
const toFlatObject = (sourceObj, destObj, filter2, propFilter) => {
  let props;
  let i;
  let prop;
  const merged = {};
  destObj = destObj || {};
  if (sourceObj == null)
    return destObj;
  do {
    props = Object.getOwnPropertyNames(sourceObj);
    i = props.length;
    while (i-- > 0) {
      prop = props[i];
      if ((!propFilter || propFilter(prop, sourceObj, destObj)) && !merged[prop]) {
        destObj[prop] = sourceObj[prop];
        merged[prop] = true;
      }
    }
    sourceObj = filter2 !== false && getPrototypeOf(sourceObj);
  } while (sourceObj && (!filter2 || filter2(sourceObj, destObj)) && sourceObj !== Object.prototype);
  return destObj;
};
const endsWith = (str, searchString, position) => {
  str = String(str);
  if (position === void 0 || position > str.length) {
    position = str.length;
  }
  position -= searchString.length;
  const lastIndex = str.indexOf(searchString, position);
  return lastIndex !== -1 && lastIndex === position;
};
const toArray = (thing) => {
  if (!thing)
    return null;
  if (isArray(thing))
    return thing;
  let i = thing.length;
  if (!isNumber(i))
    return null;
  const arr = new Array(i);
  while (i-- > 0) {
    arr[i] = thing[i];
  }
  return arr;
};
const isTypedArray = ((TypedArray) => {
  return (thing) => {
    return TypedArray && thing instanceof TypedArray;
  };
})(typeof Uint8Array !== "undefined" && getPrototypeOf(Uint8Array));
const forEachEntry = (obj, fn) => {
  const generator = obj && obj[Symbol.iterator];
  const iterator = generator.call(obj);
  let result;
  while ((result = iterator.next()) && !result.done) {
    const pair = result.value;
    fn.call(obj, pair[0], pair[1]);
  }
};
const matchAll = (regExp, str) => {
  let matches;
  const arr = [];
  while ((matches = regExp.exec(str)) !== null) {
    arr.push(matches);
  }
  return arr;
};
const isHTMLForm = kindOfTest("HTMLFormElement");
const toCamelCase = (str) => {
  return str.toLowerCase().replace(/[_-\s]([a-z\d])(\w*)/g, function replacer(m, p1, p2) {
    return p1.toUpperCase() + p2;
  });
};
const hasOwnProperty = (({hasOwnProperty: hasOwnProperty2}) => (obj, prop) => hasOwnProperty2.call(obj, prop))(Object.prototype);
const isRegExp = kindOfTest("RegExp");
const reduceDescriptors = (obj, reducer) => {
  const descriptors2 = Object.getOwnPropertyDescriptors(obj);
  const reducedDescriptors = {};
  forEach(descriptors2, (descriptor, name) => {
    if (reducer(descriptor, name, obj) !== false) {
      reducedDescriptors[name] = descriptor;
    }
  });
  Object.defineProperties(obj, reducedDescriptors);
};
const freezeMethods = (obj) => {
  reduceDescriptors(obj, (descriptor, name) => {
    if (isFunction(obj) && ["arguments", "caller", "callee"].indexOf(name) !== -1) {
      return false;
    }
    const value = obj[name];
    if (!isFunction(value))
      return;
    descriptor.enumerable = false;
    if ("writable" in descriptor) {
      descriptor.writable = false;
      return;
    }
    if (!descriptor.set) {
      descriptor.set = () => {
        throw Error("Can not rewrite read-only method '" + name + "'");
      };
    }
  });
};
const toObjectSet = (arrayOrString, delimiter) => {
  const obj = {};
  const define = (arr) => {
    arr.forEach((value) => {
      obj[value] = true;
    });
  };
  isArray(arrayOrString) ? define(arrayOrString) : define(String(arrayOrString).split(delimiter));
  return obj;
};
const noop$1 = () => {
};
const toFiniteNumber = (value, defaultValue) => {
  value = +value;
  return Number.isFinite(value) ? value : defaultValue;
};
const toJSONObject = (obj) => {
  const stack = new Array(10);
  const visit = (source, i) => {
    if (isObject(source)) {
      if (stack.indexOf(source) >= 0) {
        return;
      }
      if (!("toJSON" in source)) {
        stack[i] = source;
        const target = isArray(source) ? [] : {};
        forEach(source, (value, key) => {
          const reducedValue = visit(value, i + 1);
          !isUndefined(reducedValue) && (target[key] = reducedValue);
        });
        stack[i] = void 0;
        return target;
      }
    }
    return source;
  };
  return visit(obj, 0);
};
var utils = {
  isArray,
  isArrayBuffer,
  isBuffer,
  isFormData,
  isArrayBufferView,
  isString,
  isNumber,
  isBoolean,
  isObject,
  isPlainObject,
  isUndefined,
  isDate,
  isFile,
  isBlob,
  isRegExp,
  isFunction,
  isStream,
  isURLSearchParams,
  isTypedArray,
  isFileList,
  forEach,
  merge,
  extend,
  trim,
  stripBOM,
  inherits,
  toFlatObject,
  kindOf,
  kindOfTest,
  endsWith,
  toArray,
  forEachEntry,
  matchAll,
  isHTMLForm,
  hasOwnProperty,
  hasOwnProp: hasOwnProperty,
  reduceDescriptors,
  freezeMethods,
  toObjectSet,
  toCamelCase,
  noop: noop$1,
  toFiniteNumber,
  findKey,
  global: _global,
  isContextDefined,
  toJSONObject
};
var lookup = [];
var revLookup = [];
var Arr = typeof Uint8Array !== "undefined" ? Uint8Array : Array;
var inited = false;
function init$1() {
  inited = true;
  var code = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  for (var i = 0, len = code.length; i < len; ++i) {
    lookup[i] = code[i];
    revLookup[code.charCodeAt(i)] = i;
  }
  revLookup["-".charCodeAt(0)] = 62;
  revLookup["_".charCodeAt(0)] = 63;
}
function toByteArray(b64) {
  if (!inited) {
    init$1();
  }
  var i, j, l, tmp, placeHolders, arr;
  var len = b64.length;
  if (len % 4 > 0) {
    throw new Error("Invalid string. Length must be a multiple of 4");
  }
  placeHolders = b64[len - 2] === "=" ? 2 : b64[len - 1] === "=" ? 1 : 0;
  arr = new Arr(len * 3 / 4 - placeHolders);
  l = placeHolders > 0 ? len - 4 : len;
  var L = 0;
  for (i = 0, j = 0; i < l; i += 4, j += 3) {
    tmp = revLookup[b64.charCodeAt(i)] << 18 | revLookup[b64.charCodeAt(i + 1)] << 12 | revLookup[b64.charCodeAt(i + 2)] << 6 | revLookup[b64.charCodeAt(i + 3)];
    arr[L++] = tmp >> 16 & 255;
    arr[L++] = tmp >> 8 & 255;
    arr[L++] = tmp & 255;
  }
  if (placeHolders === 2) {
    tmp = revLookup[b64.charCodeAt(i)] << 2 | revLookup[b64.charCodeAt(i + 1)] >> 4;
    arr[L++] = tmp & 255;
  } else if (placeHolders === 1) {
    tmp = revLookup[b64.charCodeAt(i)] << 10 | revLookup[b64.charCodeAt(i + 1)] << 4 | revLookup[b64.charCodeAt(i + 2)] >> 2;
    arr[L++] = tmp >> 8 & 255;
    arr[L++] = tmp & 255;
  }
  return arr;
}
function tripletToBase64(num) {
  return lookup[num >> 18 & 63] + lookup[num >> 12 & 63] + lookup[num >> 6 & 63] + lookup[num & 63];
}
function encodeChunk(uint8, start, end) {
  var tmp;
  var output = [];
  for (var i = start; i < end; i += 3) {
    tmp = (uint8[i] << 16) + (uint8[i + 1] << 8) + uint8[i + 2];
    output.push(tripletToBase64(tmp));
  }
  return output.join("");
}
function fromByteArray(uint8) {
  if (!inited) {
    init$1();
  }
  var tmp;
  var len = uint8.length;
  var extraBytes = len % 3;
  var output = "";
  var parts = [];
  var maxChunkLength = 16383;
  for (var i = 0, len2 = len - extraBytes; i < len2; i += maxChunkLength) {
    parts.push(encodeChunk(uint8, i, i + maxChunkLength > len2 ? len2 : i + maxChunkLength));
  }
  if (extraBytes === 1) {
    tmp = uint8[len - 1];
    output += lookup[tmp >> 2];
    output += lookup[tmp << 4 & 63];
    output += "==";
  } else if (extraBytes === 2) {
    tmp = (uint8[len - 2] << 8) + uint8[len - 1];
    output += lookup[tmp >> 10];
    output += lookup[tmp >> 4 & 63];
    output += lookup[tmp << 2 & 63];
    output += "=";
  }
  parts.push(output);
  return parts.join("");
}
function read(buffer, offset, isLE, mLen, nBytes) {
  var e, m;
  var eLen = nBytes * 8 - mLen - 1;
  var eMax = (1 << eLen) - 1;
  var eBias = eMax >> 1;
  var nBits = -7;
  var i = isLE ? nBytes - 1 : 0;
  var d = isLE ? -1 : 1;
  var s = buffer[offset + i];
  i += d;
  e = s & (1 << -nBits) - 1;
  s >>= -nBits;
  nBits += eLen;
  for (; nBits > 0; e = e * 256 + buffer[offset + i], i += d, nBits -= 8) {
  }
  m = e & (1 << -nBits) - 1;
  e >>= -nBits;
  nBits += mLen;
  for (; nBits > 0; m = m * 256 + buffer[offset + i], i += d, nBits -= 8) {
  }
  if (e === 0) {
    e = 1 - eBias;
  } else if (e === eMax) {
    return m ? NaN : (s ? -1 : 1) * Infinity;
  } else {
    m = m + Math.pow(2, mLen);
    e = e - eBias;
  }
  return (s ? -1 : 1) * m * Math.pow(2, e - mLen);
}
function write(buffer, value, offset, isLE, mLen, nBytes) {
  var e, m, c;
  var eLen = nBytes * 8 - mLen - 1;
  var eMax = (1 << eLen) - 1;
  var eBias = eMax >> 1;
  var rt = mLen === 23 ? Math.pow(2, -24) - Math.pow(2, -77) : 0;
  var i = isLE ? 0 : nBytes - 1;
  var d = isLE ? 1 : -1;
  var s = value < 0 || value === 0 && 1 / value < 0 ? 1 : 0;
  value = Math.abs(value);
  if (isNaN(value) || value === Infinity) {
    m = isNaN(value) ? 1 : 0;
    e = eMax;
  } else {
    e = Math.floor(Math.log(value) / Math.LN2);
    if (value * (c = Math.pow(2, -e)) < 1) {
      e--;
      c *= 2;
    }
    if (e + eBias >= 1) {
      value += rt / c;
    } else {
      value += rt * Math.pow(2, 1 - eBias);
    }
    if (value * c >= 2) {
      e++;
      c /= 2;
    }
    if (e + eBias >= eMax) {
      m = 0;
      e = eMax;
    } else if (e + eBias >= 1) {
      m = (value * c - 1) * Math.pow(2, mLen);
      e = e + eBias;
    } else {
      m = value * Math.pow(2, eBias - 1) * Math.pow(2, mLen);
      e = 0;
    }
  }
  for (; mLen >= 8; buffer[offset + i] = m & 255, i += d, m /= 256, mLen -= 8) {
  }
  e = e << mLen | m;
  eLen += mLen;
  for (; eLen > 0; buffer[offset + i] = e & 255, i += d, e /= 256, eLen -= 8) {
  }
  buffer[offset + i - d] |= s * 128;
}
var toString$1 = {}.toString;
var isArray$1 = Array.isArray || function(arr) {
  return toString$1.call(arr) == "[object Array]";
};
/*!
 * The buffer module from node.js, for the browser.
 *
 * @author   Feross Aboukhadijeh <feross@feross.org> <http://feross.org>
 * @license  MIT
 */
var INSPECT_MAX_BYTES = 50;
Buffer.TYPED_ARRAY_SUPPORT = global$1.TYPED_ARRAY_SUPPORT !== void 0 ? global$1.TYPED_ARRAY_SUPPORT : true;
function kMaxLength() {
  return Buffer.TYPED_ARRAY_SUPPORT ? 2147483647 : 1073741823;
}
function createBuffer(that, length) {
  if (kMaxLength() < length) {
    throw new RangeError("Invalid typed array length");
  }
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    that = new Uint8Array(length);
    that.__proto__ = Buffer.prototype;
  } else {
    if (that === null) {
      that = new Buffer(length);
    }
    that.length = length;
  }
  return that;
}
function Buffer(arg, encodingOrOffset, length) {
  if (!Buffer.TYPED_ARRAY_SUPPORT && !(this instanceof Buffer)) {
    return new Buffer(arg, encodingOrOffset, length);
  }
  if (typeof arg === "number") {
    if (typeof encodingOrOffset === "string") {
      throw new Error("If encoding is specified then the first argument must be a string");
    }
    return allocUnsafe(this, arg);
  }
  return from(this, arg, encodingOrOffset, length);
}
Buffer.poolSize = 8192;
Buffer._augment = function(arr) {
  arr.__proto__ = Buffer.prototype;
  return arr;
};
function from(that, value, encodingOrOffset, length) {
  if (typeof value === "number") {
    throw new TypeError('"value" argument must not be a number');
  }
  if (typeof ArrayBuffer !== "undefined" && value instanceof ArrayBuffer) {
    return fromArrayBuffer(that, value, encodingOrOffset, length);
  }
  if (typeof value === "string") {
    return fromString(that, value, encodingOrOffset);
  }
  return fromObject(that, value);
}
Buffer.from = function(value, encodingOrOffset, length) {
  return from(null, value, encodingOrOffset, length);
};
if (Buffer.TYPED_ARRAY_SUPPORT) {
  Buffer.prototype.__proto__ = Uint8Array.prototype;
  Buffer.__proto__ = Uint8Array;
}
function assertSize(size) {
  if (typeof size !== "number") {
    throw new TypeError('"size" argument must be a number');
  } else if (size < 0) {
    throw new RangeError('"size" argument must not be negative');
  }
}
function alloc(that, size, fill2, encoding) {
  assertSize(size);
  if (size <= 0) {
    return createBuffer(that, size);
  }
  if (fill2 !== void 0) {
    return typeof encoding === "string" ? createBuffer(that, size).fill(fill2, encoding) : createBuffer(that, size).fill(fill2);
  }
  return createBuffer(that, size);
}
Buffer.alloc = function(size, fill2, encoding) {
  return alloc(null, size, fill2, encoding);
};
function allocUnsafe(that, size) {
  assertSize(size);
  that = createBuffer(that, size < 0 ? 0 : checked(size) | 0);
  if (!Buffer.TYPED_ARRAY_SUPPORT) {
    for (var i = 0; i < size; ++i) {
      that[i] = 0;
    }
  }
  return that;
}
Buffer.allocUnsafe = function(size) {
  return allocUnsafe(null, size);
};
Buffer.allocUnsafeSlow = function(size) {
  return allocUnsafe(null, size);
};
function fromString(that, string, encoding) {
  if (typeof encoding !== "string" || encoding === "") {
    encoding = "utf8";
  }
  if (!Buffer.isEncoding(encoding)) {
    throw new TypeError('"encoding" must be a valid string encoding');
  }
  var length = byteLength(string, encoding) | 0;
  that = createBuffer(that, length);
  var actual = that.write(string, encoding);
  if (actual !== length) {
    that = that.slice(0, actual);
  }
  return that;
}
function fromArrayLike(that, array) {
  var length = array.length < 0 ? 0 : checked(array.length) | 0;
  that = createBuffer(that, length);
  for (var i = 0; i < length; i += 1) {
    that[i] = array[i] & 255;
  }
  return that;
}
function fromArrayBuffer(that, array, byteOffset, length) {
  array.byteLength;
  if (byteOffset < 0 || array.byteLength < byteOffset) {
    throw new RangeError("'offset' is out of bounds");
  }
  if (array.byteLength < byteOffset + (length || 0)) {
    throw new RangeError("'length' is out of bounds");
  }
  if (byteOffset === void 0 && length === void 0) {
    array = new Uint8Array(array);
  } else if (length === void 0) {
    array = new Uint8Array(array, byteOffset);
  } else {
    array = new Uint8Array(array, byteOffset, length);
  }
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    that = array;
    that.__proto__ = Buffer.prototype;
  } else {
    that = fromArrayLike(that, array);
  }
  return that;
}
function fromObject(that, obj) {
  if (internalIsBuffer(obj)) {
    var len = checked(obj.length) | 0;
    that = createBuffer(that, len);
    if (that.length === 0) {
      return that;
    }
    obj.copy(that, 0, 0, len);
    return that;
  }
  if (obj) {
    if (typeof ArrayBuffer !== "undefined" && obj.buffer instanceof ArrayBuffer || "length" in obj) {
      if (typeof obj.length !== "number" || isnan(obj.length)) {
        return createBuffer(that, 0);
      }
      return fromArrayLike(that, obj);
    }
    if (obj.type === "Buffer" && isArray$1(obj.data)) {
      return fromArrayLike(that, obj.data);
    }
  }
  throw new TypeError("First argument must be a string, Buffer, ArrayBuffer, Array, or array-like object.");
}
function checked(length) {
  if (length >= kMaxLength()) {
    throw new RangeError("Attempt to allocate Buffer larger than maximum size: 0x" + kMaxLength().toString(16) + " bytes");
  }
  return length | 0;
}
Buffer.isBuffer = isBuffer$1;
function internalIsBuffer(b) {
  return !!(b != null && b._isBuffer);
}
Buffer.compare = function compare(a, b) {
  if (!internalIsBuffer(a) || !internalIsBuffer(b)) {
    throw new TypeError("Arguments must be Buffers");
  }
  if (a === b)
    return 0;
  var x = a.length;
  var y = b.length;
  for (var i = 0, len = Math.min(x, y); i < len; ++i) {
    if (a[i] !== b[i]) {
      x = a[i];
      y = b[i];
      break;
    }
  }
  if (x < y)
    return -1;
  if (y < x)
    return 1;
  return 0;
};
Buffer.isEncoding = function isEncoding(encoding) {
  switch (String(encoding).toLowerCase()) {
    case "hex":
    case "utf8":
    case "utf-8":
    case "ascii":
    case "latin1":
    case "binary":
    case "base64":
    case "ucs2":
    case "ucs-2":
    case "utf16le":
    case "utf-16le":
      return true;
    default:
      return false;
  }
};
Buffer.concat = function concat(list, length) {
  if (!isArray$1(list)) {
    throw new TypeError('"list" argument must be an Array of Buffers');
  }
  if (list.length === 0) {
    return Buffer.alloc(0);
  }
  var i;
  if (length === void 0) {
    length = 0;
    for (i = 0; i < list.length; ++i) {
      length += list[i].length;
    }
  }
  var buffer = Buffer.allocUnsafe(length);
  var pos = 0;
  for (i = 0; i < list.length; ++i) {
    var buf = list[i];
    if (!internalIsBuffer(buf)) {
      throw new TypeError('"list" argument must be an Array of Buffers');
    }
    buf.copy(buffer, pos);
    pos += buf.length;
  }
  return buffer;
};
function byteLength(string, encoding) {
  if (internalIsBuffer(string)) {
    return string.length;
  }
  if (typeof ArrayBuffer !== "undefined" && typeof ArrayBuffer.isView === "function" && (ArrayBuffer.isView(string) || string instanceof ArrayBuffer)) {
    return string.byteLength;
  }
  if (typeof string !== "string") {
    string = "" + string;
  }
  var len = string.length;
  if (len === 0)
    return 0;
  var loweredCase = false;
  for (; ; ) {
    switch (encoding) {
      case "ascii":
      case "latin1":
      case "binary":
        return len;
      case "utf8":
      case "utf-8":
      case void 0:
        return utf8ToBytes(string).length;
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return len * 2;
      case "hex":
        return len >>> 1;
      case "base64":
        return base64ToBytes(string).length;
      default:
        if (loweredCase)
          return utf8ToBytes(string).length;
        encoding = ("" + encoding).toLowerCase();
        loweredCase = true;
    }
  }
}
Buffer.byteLength = byteLength;
function slowToString(encoding, start, end) {
  var loweredCase = false;
  if (start === void 0 || start < 0) {
    start = 0;
  }
  if (start > this.length) {
    return "";
  }
  if (end === void 0 || end > this.length) {
    end = this.length;
  }
  if (end <= 0) {
    return "";
  }
  end >>>= 0;
  start >>>= 0;
  if (end <= start) {
    return "";
  }
  if (!encoding)
    encoding = "utf8";
  while (true) {
    switch (encoding) {
      case "hex":
        return hexSlice(this, start, end);
      case "utf8":
      case "utf-8":
        return utf8Slice(this, start, end);
      case "ascii":
        return asciiSlice(this, start, end);
      case "latin1":
      case "binary":
        return latin1Slice(this, start, end);
      case "base64":
        return base64Slice(this, start, end);
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return utf16leSlice(this, start, end);
      default:
        if (loweredCase)
          throw new TypeError("Unknown encoding: " + encoding);
        encoding = (encoding + "").toLowerCase();
        loweredCase = true;
    }
  }
}
Buffer.prototype._isBuffer = true;
function swap(b, n, m) {
  var i = b[n];
  b[n] = b[m];
  b[m] = i;
}
Buffer.prototype.swap16 = function swap16() {
  var len = this.length;
  if (len % 2 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 16-bits");
  }
  for (var i = 0; i < len; i += 2) {
    swap(this, i, i + 1);
  }
  return this;
};
Buffer.prototype.swap32 = function swap32() {
  var len = this.length;
  if (len % 4 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 32-bits");
  }
  for (var i = 0; i < len; i += 4) {
    swap(this, i, i + 3);
    swap(this, i + 1, i + 2);
  }
  return this;
};
Buffer.prototype.swap64 = function swap64() {
  var len = this.length;
  if (len % 8 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 64-bits");
  }
  for (var i = 0; i < len; i += 8) {
    swap(this, i, i + 7);
    swap(this, i + 1, i + 6);
    swap(this, i + 2, i + 5);
    swap(this, i + 3, i + 4);
  }
  return this;
};
Buffer.prototype.toString = function toString2() {
  var length = this.length | 0;
  if (length === 0)
    return "";
  if (arguments.length === 0)
    return utf8Slice(this, 0, length);
  return slowToString.apply(this, arguments);
};
Buffer.prototype.equals = function equals(b) {
  if (!internalIsBuffer(b))
    throw new TypeError("Argument must be a Buffer");
  if (this === b)
    return true;
  return Buffer.compare(this, b) === 0;
};
Buffer.prototype.inspect = function inspect() {
  var str = "";
  var max = INSPECT_MAX_BYTES;
  if (this.length > 0) {
    str = this.toString("hex", 0, max).match(/.{2}/g).join(" ");
    if (this.length > max)
      str += " ... ";
  }
  return "<Buffer " + str + ">";
};
Buffer.prototype.compare = function compare2(target, start, end, thisStart, thisEnd) {
  if (!internalIsBuffer(target)) {
    throw new TypeError("Argument must be a Buffer");
  }
  if (start === void 0) {
    start = 0;
  }
  if (end === void 0) {
    end = target ? target.length : 0;
  }
  if (thisStart === void 0) {
    thisStart = 0;
  }
  if (thisEnd === void 0) {
    thisEnd = this.length;
  }
  if (start < 0 || end > target.length || thisStart < 0 || thisEnd > this.length) {
    throw new RangeError("out of range index");
  }
  if (thisStart >= thisEnd && start >= end) {
    return 0;
  }
  if (thisStart >= thisEnd) {
    return -1;
  }
  if (start >= end) {
    return 1;
  }
  start >>>= 0;
  end >>>= 0;
  thisStart >>>= 0;
  thisEnd >>>= 0;
  if (this === target)
    return 0;
  var x = thisEnd - thisStart;
  var y = end - start;
  var len = Math.min(x, y);
  var thisCopy = this.slice(thisStart, thisEnd);
  var targetCopy = target.slice(start, end);
  for (var i = 0; i < len; ++i) {
    if (thisCopy[i] !== targetCopy[i]) {
      x = thisCopy[i];
      y = targetCopy[i];
      break;
    }
  }
  if (x < y)
    return -1;
  if (y < x)
    return 1;
  return 0;
};
function bidirectionalIndexOf(buffer, val, byteOffset, encoding, dir) {
  if (buffer.length === 0)
    return -1;
  if (typeof byteOffset === "string") {
    encoding = byteOffset;
    byteOffset = 0;
  } else if (byteOffset > 2147483647) {
    byteOffset = 2147483647;
  } else if (byteOffset < -2147483648) {
    byteOffset = -2147483648;
  }
  byteOffset = +byteOffset;
  if (isNaN(byteOffset)) {
    byteOffset = dir ? 0 : buffer.length - 1;
  }
  if (byteOffset < 0)
    byteOffset = buffer.length + byteOffset;
  if (byteOffset >= buffer.length) {
    if (dir)
      return -1;
    else
      byteOffset = buffer.length - 1;
  } else if (byteOffset < 0) {
    if (dir)
      byteOffset = 0;
    else
      return -1;
  }
  if (typeof val === "string") {
    val = Buffer.from(val, encoding);
  }
  if (internalIsBuffer(val)) {
    if (val.length === 0) {
      return -1;
    }
    return arrayIndexOf(buffer, val, byteOffset, encoding, dir);
  } else if (typeof val === "number") {
    val = val & 255;
    if (Buffer.TYPED_ARRAY_SUPPORT && typeof Uint8Array.prototype.indexOf === "function") {
      if (dir) {
        return Uint8Array.prototype.indexOf.call(buffer, val, byteOffset);
      } else {
        return Uint8Array.prototype.lastIndexOf.call(buffer, val, byteOffset);
      }
    }
    return arrayIndexOf(buffer, [val], byteOffset, encoding, dir);
  }
  throw new TypeError("val must be string, number or Buffer");
}
function arrayIndexOf(arr, val, byteOffset, encoding, dir) {
  var indexSize = 1;
  var arrLength = arr.length;
  var valLength = val.length;
  if (encoding !== void 0) {
    encoding = String(encoding).toLowerCase();
    if (encoding === "ucs2" || encoding === "ucs-2" || encoding === "utf16le" || encoding === "utf-16le") {
      if (arr.length < 2 || val.length < 2) {
        return -1;
      }
      indexSize = 2;
      arrLength /= 2;
      valLength /= 2;
      byteOffset /= 2;
    }
  }
  function read2(buf, i2) {
    if (indexSize === 1) {
      return buf[i2];
    } else {
      return buf.readUInt16BE(i2 * indexSize);
    }
  }
  var i;
  if (dir) {
    var foundIndex = -1;
    for (i = byteOffset; i < arrLength; i++) {
      if (read2(arr, i) === read2(val, foundIndex === -1 ? 0 : i - foundIndex)) {
        if (foundIndex === -1)
          foundIndex = i;
        if (i - foundIndex + 1 === valLength)
          return foundIndex * indexSize;
      } else {
        if (foundIndex !== -1)
          i -= i - foundIndex;
        foundIndex = -1;
      }
    }
  } else {
    if (byteOffset + valLength > arrLength)
      byteOffset = arrLength - valLength;
    for (i = byteOffset; i >= 0; i--) {
      var found = true;
      for (var j = 0; j < valLength; j++) {
        if (read2(arr, i + j) !== read2(val, j)) {
          found = false;
          break;
        }
      }
      if (found)
        return i;
    }
  }
  return -1;
}
Buffer.prototype.includes = function includes(val, byteOffset, encoding) {
  return this.indexOf(val, byteOffset, encoding) !== -1;
};
Buffer.prototype.indexOf = function indexOf(val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, true);
};
Buffer.prototype.lastIndexOf = function lastIndexOf(val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, false);
};
function hexWrite(buf, string, offset, length) {
  offset = Number(offset) || 0;
  var remaining = buf.length - offset;
  if (!length) {
    length = remaining;
  } else {
    length = Number(length);
    if (length > remaining) {
      length = remaining;
    }
  }
  var strLen = string.length;
  if (strLen % 2 !== 0)
    throw new TypeError("Invalid hex string");
  if (length > strLen / 2) {
    length = strLen / 2;
  }
  for (var i = 0; i < length; ++i) {
    var parsed = parseInt(string.substr(i * 2, 2), 16);
    if (isNaN(parsed))
      return i;
    buf[offset + i] = parsed;
  }
  return i;
}
function utf8Write(buf, string, offset, length) {
  return blitBuffer(utf8ToBytes(string, buf.length - offset), buf, offset, length);
}
function asciiWrite(buf, string, offset, length) {
  return blitBuffer(asciiToBytes(string), buf, offset, length);
}
function latin1Write(buf, string, offset, length) {
  return asciiWrite(buf, string, offset, length);
}
function base64Write(buf, string, offset, length) {
  return blitBuffer(base64ToBytes(string), buf, offset, length);
}
function ucs2Write(buf, string, offset, length) {
  return blitBuffer(utf16leToBytes(string, buf.length - offset), buf, offset, length);
}
Buffer.prototype.write = function write2(string, offset, length, encoding) {
  if (offset === void 0) {
    encoding = "utf8";
    length = this.length;
    offset = 0;
  } else if (length === void 0 && typeof offset === "string") {
    encoding = offset;
    length = this.length;
    offset = 0;
  } else if (isFinite(offset)) {
    offset = offset | 0;
    if (isFinite(length)) {
      length = length | 0;
      if (encoding === void 0)
        encoding = "utf8";
    } else {
      encoding = length;
      length = void 0;
    }
  } else {
    throw new Error("Buffer.write(string, encoding, offset[, length]) is no longer supported");
  }
  var remaining = this.length - offset;
  if (length === void 0 || length > remaining)
    length = remaining;
  if (string.length > 0 && (length < 0 || offset < 0) || offset > this.length) {
    throw new RangeError("Attempt to write outside buffer bounds");
  }
  if (!encoding)
    encoding = "utf8";
  var loweredCase = false;
  for (; ; ) {
    switch (encoding) {
      case "hex":
        return hexWrite(this, string, offset, length);
      case "utf8":
      case "utf-8":
        return utf8Write(this, string, offset, length);
      case "ascii":
        return asciiWrite(this, string, offset, length);
      case "latin1":
      case "binary":
        return latin1Write(this, string, offset, length);
      case "base64":
        return base64Write(this, string, offset, length);
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return ucs2Write(this, string, offset, length);
      default:
        if (loweredCase)
          throw new TypeError("Unknown encoding: " + encoding);
        encoding = ("" + encoding).toLowerCase();
        loweredCase = true;
    }
  }
};
Buffer.prototype.toJSON = function toJSON() {
  return {
    type: "Buffer",
    data: Array.prototype.slice.call(this._arr || this, 0)
  };
};
function base64Slice(buf, start, end) {
  if (start === 0 && end === buf.length) {
    return fromByteArray(buf);
  } else {
    return fromByteArray(buf.slice(start, end));
  }
}
function utf8Slice(buf, start, end) {
  end = Math.min(buf.length, end);
  var res = [];
  var i = start;
  while (i < end) {
    var firstByte = buf[i];
    var codePoint = null;
    var bytesPerSequence = firstByte > 239 ? 4 : firstByte > 223 ? 3 : firstByte > 191 ? 2 : 1;
    if (i + bytesPerSequence <= end) {
      var secondByte, thirdByte, fourthByte, tempCodePoint;
      switch (bytesPerSequence) {
        case 1:
          if (firstByte < 128) {
            codePoint = firstByte;
          }
          break;
        case 2:
          secondByte = buf[i + 1];
          if ((secondByte & 192) === 128) {
            tempCodePoint = (firstByte & 31) << 6 | secondByte & 63;
            if (tempCodePoint > 127) {
              codePoint = tempCodePoint;
            }
          }
          break;
        case 3:
          secondByte = buf[i + 1];
          thirdByte = buf[i + 2];
          if ((secondByte & 192) === 128 && (thirdByte & 192) === 128) {
            tempCodePoint = (firstByte & 15) << 12 | (secondByte & 63) << 6 | thirdByte & 63;
            if (tempCodePoint > 2047 && (tempCodePoint < 55296 || tempCodePoint > 57343)) {
              codePoint = tempCodePoint;
            }
          }
          break;
        case 4:
          secondByte = buf[i + 1];
          thirdByte = buf[i + 2];
          fourthByte = buf[i + 3];
          if ((secondByte & 192) === 128 && (thirdByte & 192) === 128 && (fourthByte & 192) === 128) {
            tempCodePoint = (firstByte & 15) << 18 | (secondByte & 63) << 12 | (thirdByte & 63) << 6 | fourthByte & 63;
            if (tempCodePoint > 65535 && tempCodePoint < 1114112) {
              codePoint = tempCodePoint;
            }
          }
      }
    }
    if (codePoint === null) {
      codePoint = 65533;
      bytesPerSequence = 1;
    } else if (codePoint > 65535) {
      codePoint -= 65536;
      res.push(codePoint >>> 10 & 1023 | 55296);
      codePoint = 56320 | codePoint & 1023;
    }
    res.push(codePoint);
    i += bytesPerSequence;
  }
  return decodeCodePointsArray(res);
}
var MAX_ARGUMENTS_LENGTH = 4096;
function decodeCodePointsArray(codePoints) {
  var len = codePoints.length;
  if (len <= MAX_ARGUMENTS_LENGTH) {
    return String.fromCharCode.apply(String, codePoints);
  }
  var res = "";
  var i = 0;
  while (i < len) {
    res += String.fromCharCode.apply(String, codePoints.slice(i, i += MAX_ARGUMENTS_LENGTH));
  }
  return res;
}
function asciiSlice(buf, start, end) {
  var ret = "";
  end = Math.min(buf.length, end);
  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i] & 127);
  }
  return ret;
}
function latin1Slice(buf, start, end) {
  var ret = "";
  end = Math.min(buf.length, end);
  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i]);
  }
  return ret;
}
function hexSlice(buf, start, end) {
  var len = buf.length;
  if (!start || start < 0)
    start = 0;
  if (!end || end < 0 || end > len)
    end = len;
  var out = "";
  for (var i = start; i < end; ++i) {
    out += toHex(buf[i]);
  }
  return out;
}
function utf16leSlice(buf, start, end) {
  var bytes = buf.slice(start, end);
  var res = "";
  for (var i = 0; i < bytes.length; i += 2) {
    res += String.fromCharCode(bytes[i] + bytes[i + 1] * 256);
  }
  return res;
}
Buffer.prototype.slice = function slice(start, end) {
  var len = this.length;
  start = ~~start;
  end = end === void 0 ? len : ~~end;
  if (start < 0) {
    start += len;
    if (start < 0)
      start = 0;
  } else if (start > len) {
    start = len;
  }
  if (end < 0) {
    end += len;
    if (end < 0)
      end = 0;
  } else if (end > len) {
    end = len;
  }
  if (end < start)
    end = start;
  var newBuf;
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    newBuf = this.subarray(start, end);
    newBuf.__proto__ = Buffer.prototype;
  } else {
    var sliceLen = end - start;
    newBuf = new Buffer(sliceLen, void 0);
    for (var i = 0; i < sliceLen; ++i) {
      newBuf[i] = this[i + start];
    }
  }
  return newBuf;
};
function checkOffset(offset, ext, length) {
  if (offset % 1 !== 0 || offset < 0)
    throw new RangeError("offset is not uint");
  if (offset + ext > length)
    throw new RangeError("Trying to access beyond buffer length");
}
Buffer.prototype.readUIntLE = function readUIntLE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var val = this[offset];
  var mul = 1;
  var i = 0;
  while (++i < byteLength2 && (mul *= 256)) {
    val += this[offset + i] * mul;
  }
  return val;
};
Buffer.prototype.readUIntBE = function readUIntBE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    checkOffset(offset, byteLength2, this.length);
  }
  var val = this[offset + --byteLength2];
  var mul = 1;
  while (byteLength2 > 0 && (mul *= 256)) {
    val += this[offset + --byteLength2] * mul;
  }
  return val;
};
Buffer.prototype.readUInt8 = function readUInt8(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 1, this.length);
  return this[offset];
};
Buffer.prototype.readUInt16LE = function readUInt16LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  return this[offset] | this[offset + 1] << 8;
};
Buffer.prototype.readUInt16BE = function readUInt16BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  return this[offset] << 8 | this[offset + 1];
};
Buffer.prototype.readUInt32LE = function readUInt32LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return (this[offset] | this[offset + 1] << 8 | this[offset + 2] << 16) + this[offset + 3] * 16777216;
};
Buffer.prototype.readUInt32BE = function readUInt32BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] * 16777216 + (this[offset + 1] << 16 | this[offset + 2] << 8 | this[offset + 3]);
};
Buffer.prototype.readIntLE = function readIntLE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var val = this[offset];
  var mul = 1;
  var i = 0;
  while (++i < byteLength2 && (mul *= 256)) {
    val += this[offset + i] * mul;
  }
  mul *= 128;
  if (val >= mul)
    val -= Math.pow(2, 8 * byteLength2);
  return val;
};
Buffer.prototype.readIntBE = function readIntBE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var i = byteLength2;
  var mul = 1;
  var val = this[offset + --i];
  while (i > 0 && (mul *= 256)) {
    val += this[offset + --i] * mul;
  }
  mul *= 128;
  if (val >= mul)
    val -= Math.pow(2, 8 * byteLength2);
  return val;
};
Buffer.prototype.readInt8 = function readInt8(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 1, this.length);
  if (!(this[offset] & 128))
    return this[offset];
  return (255 - this[offset] + 1) * -1;
};
Buffer.prototype.readInt16LE = function readInt16LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  var val = this[offset] | this[offset + 1] << 8;
  return val & 32768 ? val | 4294901760 : val;
};
Buffer.prototype.readInt16BE = function readInt16BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  var val = this[offset + 1] | this[offset] << 8;
  return val & 32768 ? val | 4294901760 : val;
};
Buffer.prototype.readInt32LE = function readInt32LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] | this[offset + 1] << 8 | this[offset + 2] << 16 | this[offset + 3] << 24;
};
Buffer.prototype.readInt32BE = function readInt32BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] << 24 | this[offset + 1] << 16 | this[offset + 2] << 8 | this[offset + 3];
};
Buffer.prototype.readFloatLE = function readFloatLE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return read(this, offset, true, 23, 4);
};
Buffer.prototype.readFloatBE = function readFloatBE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return read(this, offset, false, 23, 4);
};
Buffer.prototype.readDoubleLE = function readDoubleLE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 8, this.length);
  return read(this, offset, true, 52, 8);
};
Buffer.prototype.readDoubleBE = function readDoubleBE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 8, this.length);
  return read(this, offset, false, 52, 8);
};
function checkInt(buf, value, offset, ext, max, min) {
  if (!internalIsBuffer(buf))
    throw new TypeError('"buffer" argument must be a Buffer instance');
  if (value > max || value < min)
    throw new RangeError('"value" argument is out of bounds');
  if (offset + ext > buf.length)
    throw new RangeError("Index out of range");
}
Buffer.prototype.writeUIntLE = function writeUIntLE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength2) - 1;
    checkInt(this, value, offset, byteLength2, maxBytes, 0);
  }
  var mul = 1;
  var i = 0;
  this[offset] = value & 255;
  while (++i < byteLength2 && (mul *= 256)) {
    this[offset + i] = value / mul & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeUIntBE = function writeUIntBE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength2) - 1;
    checkInt(this, value, offset, byteLength2, maxBytes, 0);
  }
  var i = byteLength2 - 1;
  var mul = 1;
  this[offset + i] = value & 255;
  while (--i >= 0 && (mul *= 256)) {
    this[offset + i] = value / mul & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeUInt8 = function writeUInt8(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 1, 255, 0);
  if (!Buffer.TYPED_ARRAY_SUPPORT)
    value = Math.floor(value);
  this[offset] = value & 255;
  return offset + 1;
};
function objectWriteUInt16(buf, value, offset, littleEndian) {
  if (value < 0)
    value = 65535 + value + 1;
  for (var i = 0, j = Math.min(buf.length - offset, 2); i < j; ++i) {
    buf[offset + i] = (value & 255 << 8 * (littleEndian ? i : 1 - i)) >>> (littleEndian ? i : 1 - i) * 8;
  }
}
Buffer.prototype.writeUInt16LE = function writeUInt16LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 65535, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
  } else {
    objectWriteUInt16(this, value, offset, true);
  }
  return offset + 2;
};
Buffer.prototype.writeUInt16BE = function writeUInt16BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 65535, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 8;
    this[offset + 1] = value & 255;
  } else {
    objectWriteUInt16(this, value, offset, false);
  }
  return offset + 2;
};
function objectWriteUInt32(buf, value, offset, littleEndian) {
  if (value < 0)
    value = 4294967295 + value + 1;
  for (var i = 0, j = Math.min(buf.length - offset, 4); i < j; ++i) {
    buf[offset + i] = value >>> (littleEndian ? i : 3 - i) * 8 & 255;
  }
}
Buffer.prototype.writeUInt32LE = function writeUInt32LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 4294967295, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset + 3] = value >>> 24;
    this[offset + 2] = value >>> 16;
    this[offset + 1] = value >>> 8;
    this[offset] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, true);
  }
  return offset + 4;
};
Buffer.prototype.writeUInt32BE = function writeUInt32BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 4294967295, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 24;
    this[offset + 1] = value >>> 16;
    this[offset + 2] = value >>> 8;
    this[offset + 3] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, false);
  }
  return offset + 4;
};
Buffer.prototype.writeIntLE = function writeIntLE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert) {
    var limit = Math.pow(2, 8 * byteLength2 - 1);
    checkInt(this, value, offset, byteLength2, limit - 1, -limit);
  }
  var i = 0;
  var mul = 1;
  var sub = 0;
  this[offset] = value & 255;
  while (++i < byteLength2 && (mul *= 256)) {
    if (value < 0 && sub === 0 && this[offset + i - 1] !== 0) {
      sub = 1;
    }
    this[offset + i] = (value / mul >> 0) - sub & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeIntBE = function writeIntBE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert) {
    var limit = Math.pow(2, 8 * byteLength2 - 1);
    checkInt(this, value, offset, byteLength2, limit - 1, -limit);
  }
  var i = byteLength2 - 1;
  var mul = 1;
  var sub = 0;
  this[offset + i] = value & 255;
  while (--i >= 0 && (mul *= 256)) {
    if (value < 0 && sub === 0 && this[offset + i + 1] !== 0) {
      sub = 1;
    }
    this[offset + i] = (value / mul >> 0) - sub & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeInt8 = function writeInt8(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 1, 127, -128);
  if (!Buffer.TYPED_ARRAY_SUPPORT)
    value = Math.floor(value);
  if (value < 0)
    value = 255 + value + 1;
  this[offset] = value & 255;
  return offset + 1;
};
Buffer.prototype.writeInt16LE = function writeInt16LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 32767, -32768);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
  } else {
    objectWriteUInt16(this, value, offset, true);
  }
  return offset + 2;
};
Buffer.prototype.writeInt16BE = function writeInt16BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 32767, -32768);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 8;
    this[offset + 1] = value & 255;
  } else {
    objectWriteUInt16(this, value, offset, false);
  }
  return offset + 2;
};
Buffer.prototype.writeInt32LE = function writeInt32LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 2147483647, -2147483648);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
    this[offset + 2] = value >>> 16;
    this[offset + 3] = value >>> 24;
  } else {
    objectWriteUInt32(this, value, offset, true);
  }
  return offset + 4;
};
Buffer.prototype.writeInt32BE = function writeInt32BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 2147483647, -2147483648);
  if (value < 0)
    value = 4294967295 + value + 1;
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 24;
    this[offset + 1] = value >>> 16;
    this[offset + 2] = value >>> 8;
    this[offset + 3] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, false);
  }
  return offset + 4;
};
function checkIEEE754(buf, value, offset, ext, max, min) {
  if (offset + ext > buf.length)
    throw new RangeError("Index out of range");
  if (offset < 0)
    throw new RangeError("Index out of range");
}
function writeFloat(buf, value, offset, littleEndian, noAssert) {
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 4);
  }
  write(buf, value, offset, littleEndian, 23, 4);
  return offset + 4;
}
Buffer.prototype.writeFloatLE = function writeFloatLE(value, offset, noAssert) {
  return writeFloat(this, value, offset, true, noAssert);
};
Buffer.prototype.writeFloatBE = function writeFloatBE(value, offset, noAssert) {
  return writeFloat(this, value, offset, false, noAssert);
};
function writeDouble(buf, value, offset, littleEndian, noAssert) {
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 8);
  }
  write(buf, value, offset, littleEndian, 52, 8);
  return offset + 8;
}
Buffer.prototype.writeDoubleLE = function writeDoubleLE(value, offset, noAssert) {
  return writeDouble(this, value, offset, true, noAssert);
};
Buffer.prototype.writeDoubleBE = function writeDoubleBE(value, offset, noAssert) {
  return writeDouble(this, value, offset, false, noAssert);
};
Buffer.prototype.copy = function copy(target, targetStart, start, end) {
  if (!start)
    start = 0;
  if (!end && end !== 0)
    end = this.length;
  if (targetStart >= target.length)
    targetStart = target.length;
  if (!targetStart)
    targetStart = 0;
  if (end > 0 && end < start)
    end = start;
  if (end === start)
    return 0;
  if (target.length === 0 || this.length === 0)
    return 0;
  if (targetStart < 0) {
    throw new RangeError("targetStart out of bounds");
  }
  if (start < 0 || start >= this.length)
    throw new RangeError("sourceStart out of bounds");
  if (end < 0)
    throw new RangeError("sourceEnd out of bounds");
  if (end > this.length)
    end = this.length;
  if (target.length - targetStart < end - start) {
    end = target.length - targetStart + start;
  }
  var len = end - start;
  var i;
  if (this === target && start < targetStart && targetStart < end) {
    for (i = len - 1; i >= 0; --i) {
      target[i + targetStart] = this[i + start];
    }
  } else if (len < 1e3 || !Buffer.TYPED_ARRAY_SUPPORT) {
    for (i = 0; i < len; ++i) {
      target[i + targetStart] = this[i + start];
    }
  } else {
    Uint8Array.prototype.set.call(target, this.subarray(start, start + len), targetStart);
  }
  return len;
};
Buffer.prototype.fill = function fill(val, start, end, encoding) {
  if (typeof val === "string") {
    if (typeof start === "string") {
      encoding = start;
      start = 0;
      end = this.length;
    } else if (typeof end === "string") {
      encoding = end;
      end = this.length;
    }
    if (val.length === 1) {
      var code = val.charCodeAt(0);
      if (code < 256) {
        val = code;
      }
    }
    if (encoding !== void 0 && typeof encoding !== "string") {
      throw new TypeError("encoding must be a string");
    }
    if (typeof encoding === "string" && !Buffer.isEncoding(encoding)) {
      throw new TypeError("Unknown encoding: " + encoding);
    }
  } else if (typeof val === "number") {
    val = val & 255;
  }
  if (start < 0 || this.length < start || this.length < end) {
    throw new RangeError("Out of range index");
  }
  if (end <= start) {
    return this;
  }
  start = start >>> 0;
  end = end === void 0 ? this.length : end >>> 0;
  if (!val)
    val = 0;
  var i;
  if (typeof val === "number") {
    for (i = start; i < end; ++i) {
      this[i] = val;
    }
  } else {
    var bytes = internalIsBuffer(val) ? val : utf8ToBytes(new Buffer(val, encoding).toString());
    var len = bytes.length;
    for (i = 0; i < end - start; ++i) {
      this[i + start] = bytes[i % len];
    }
  }
  return this;
};
var INVALID_BASE64_RE = /[^+\/0-9A-Za-z-_]/g;
function base64clean(str) {
  str = stringtrim(str).replace(INVALID_BASE64_RE, "");
  if (str.length < 2)
    return "";
  while (str.length % 4 !== 0) {
    str = str + "=";
  }
  return str;
}
function stringtrim(str) {
  if (str.trim)
    return str.trim();
  return str.replace(/^\s+|\s+$/g, "");
}
function toHex(n) {
  if (n < 16)
    return "0" + n.toString(16);
  return n.toString(16);
}
function utf8ToBytes(string, units) {
  units = units || Infinity;
  var codePoint;
  var length = string.length;
  var leadSurrogate = null;
  var bytes = [];
  for (var i = 0; i < length; ++i) {
    codePoint = string.charCodeAt(i);
    if (codePoint > 55295 && codePoint < 57344) {
      if (!leadSurrogate) {
        if (codePoint > 56319) {
          if ((units -= 3) > -1)
            bytes.push(239, 191, 189);
          continue;
        } else if (i + 1 === length) {
          if ((units -= 3) > -1)
            bytes.push(239, 191, 189);
          continue;
        }
        leadSurrogate = codePoint;
        continue;
      }
      if (codePoint < 56320) {
        if ((units -= 3) > -1)
          bytes.push(239, 191, 189);
        leadSurrogate = codePoint;
        continue;
      }
      codePoint = (leadSurrogate - 55296 << 10 | codePoint - 56320) + 65536;
    } else if (leadSurrogate) {
      if ((units -= 3) > -1)
        bytes.push(239, 191, 189);
    }
    leadSurrogate = null;
    if (codePoint < 128) {
      if ((units -= 1) < 0)
        break;
      bytes.push(codePoint);
    } else if (codePoint < 2048) {
      if ((units -= 2) < 0)
        break;
      bytes.push(codePoint >> 6 | 192, codePoint & 63 | 128);
    } else if (codePoint < 65536) {
      if ((units -= 3) < 0)
        break;
      bytes.push(codePoint >> 12 | 224, codePoint >> 6 & 63 | 128, codePoint & 63 | 128);
    } else if (codePoint < 1114112) {
      if ((units -= 4) < 0)
        break;
      bytes.push(codePoint >> 18 | 240, codePoint >> 12 & 63 | 128, codePoint >> 6 & 63 | 128, codePoint & 63 | 128);
    } else {
      throw new Error("Invalid code point");
    }
  }
  return bytes;
}
function asciiToBytes(str) {
  var byteArray = [];
  for (var i = 0; i < str.length; ++i) {
    byteArray.push(str.charCodeAt(i) & 255);
  }
  return byteArray;
}
function utf16leToBytes(str, units) {
  var c, hi, lo;
  var byteArray = [];
  for (var i = 0; i < str.length; ++i) {
    if ((units -= 2) < 0)
      break;
    c = str.charCodeAt(i);
    hi = c >> 8;
    lo = c % 256;
    byteArray.push(lo);
    byteArray.push(hi);
  }
  return byteArray;
}
function base64ToBytes(str) {
  return toByteArray(base64clean(str));
}
function blitBuffer(src, dst, offset, length) {
  for (var i = 0; i < length; ++i) {
    if (i + offset >= dst.length || i >= src.length)
      break;
    dst[i + offset] = src[i];
  }
  return i;
}
function isnan(val) {
  return val !== val;
}
function isBuffer$1(obj) {
  return obj != null && (!!obj._isBuffer || isFastBuffer(obj) || isSlowBuffer(obj));
}
function isFastBuffer(obj) {
  return !!obj.constructor && typeof obj.constructor.isBuffer === "function" && obj.constructor.isBuffer(obj);
}
function isSlowBuffer(obj) {
  return typeof obj.readFloatLE === "function" && typeof obj.slice === "function" && isFastBuffer(obj.slice(0, 0));
}
function AxiosError(message, code, config, request, response) {
  Error.call(this);
  if (Error.captureStackTrace) {
    Error.captureStackTrace(this, this.constructor);
  } else {
    this.stack = new Error().stack;
  }
  this.message = message;
  this.name = "AxiosError";
  code && (this.code = code);
  config && (this.config = config);
  request && (this.request = request);
  response && (this.response = response);
}
utils.inherits(AxiosError, Error, {
  toJSON: function toJSON2() {
    return {
      message: this.message,
      name: this.name,
      description: this.description,
      number: this.number,
      fileName: this.fileName,
      lineNumber: this.lineNumber,
      columnNumber: this.columnNumber,
      stack: this.stack,
      config: utils.toJSONObject(this.config),
      code: this.code,
      status: this.response && this.response.status ? this.response.status : null
    };
  }
});
const prototype = AxiosError.prototype;
const descriptors = {};
[
  "ERR_BAD_OPTION_VALUE",
  "ERR_BAD_OPTION",
  "ECONNABORTED",
  "ETIMEDOUT",
  "ERR_NETWORK",
  "ERR_FR_TOO_MANY_REDIRECTS",
  "ERR_DEPRECATED",
  "ERR_BAD_RESPONSE",
  "ERR_BAD_REQUEST",
  "ERR_CANCELED",
  "ERR_NOT_SUPPORT",
  "ERR_INVALID_URL"
].forEach((code) => {
  descriptors[code] = {value: code};
});
Object.defineProperties(AxiosError, descriptors);
Object.defineProperty(prototype, "isAxiosError", {value: true});
AxiosError.from = (error, code, config, request, response, customProps) => {
  const axiosError = Object.create(prototype);
  utils.toFlatObject(error, axiosError, function filter2(obj) {
    return obj !== Error.prototype;
  }, (prop) => {
    return prop !== "isAxiosError";
  });
  AxiosError.call(axiosError, error.message, code, config, request, response);
  axiosError.cause = error;
  axiosError.name = error.name;
  customProps && Object.assign(axiosError, customProps);
  return axiosError;
};
function isVisitable(thing) {
  return utils.isPlainObject(thing) || utils.isArray(thing);
}
function removeBrackets(key) {
  return utils.endsWith(key, "[]") ? key.slice(0, -2) : key;
}
function renderKey(path, key, dots) {
  if (!path)
    return key;
  return path.concat(key).map(function each(token, i) {
    token = removeBrackets(token);
    return !dots && i ? "[" + token + "]" : token;
  }).join(dots ? "." : "");
}
function isFlatArray(arr) {
  return utils.isArray(arr) && !arr.some(isVisitable);
}
const predicates = utils.toFlatObject(utils, {}, null, function filter(prop) {
  return /^is[A-Z]/.test(prop);
});
function isSpecCompliant(thing) {
  return thing && utils.isFunction(thing.append) && thing[Symbol.toStringTag] === "FormData" && thing[Symbol.iterator];
}
function toFormData(obj, formData, options) {
  if (!utils.isObject(obj)) {
    throw new TypeError("target must be an object");
  }
  formData = formData || new (browser || FormData)();
  options = utils.toFlatObject(options, {
    metaTokens: true,
    dots: false,
    indexes: false
  }, false, function defined(option, source) {
    return !utils.isUndefined(source[option]);
  });
  const metaTokens = options.metaTokens;
  const visitor = options.visitor || defaultVisitor;
  const dots = options.dots;
  const indexes = options.indexes;
  const _Blob = options.Blob || typeof Blob !== "undefined" && Blob;
  const useBlob = _Blob && isSpecCompliant(formData);
  if (!utils.isFunction(visitor)) {
    throw new TypeError("visitor must be a function");
  }
  function convertValue(value) {
    if (value === null)
      return "";
    if (utils.isDate(value)) {
      return value.toISOString();
    }
    if (!useBlob && utils.isBlob(value)) {
      throw new AxiosError("Blob is not supported. Use a Buffer instead.");
    }
    if (utils.isArrayBuffer(value) || utils.isTypedArray(value)) {
      return useBlob && typeof Blob === "function" ? new Blob([value]) : Buffer.from(value);
    }
    return value;
  }
  function defaultVisitor(value, key, path) {
    let arr = value;
    if (value && !path && typeof value === "object") {
      if (utils.endsWith(key, "{}")) {
        key = metaTokens ? key : key.slice(0, -2);
        value = JSON.stringify(value);
      } else if (utils.isArray(value) && isFlatArray(value) || (utils.isFileList(value) || utils.endsWith(key, "[]") && (arr = utils.toArray(value)))) {
        key = removeBrackets(key);
        arr.forEach(function each(el, index) {
          !(utils.isUndefined(el) || el === null) && formData.append(indexes === true ? renderKey([key], index, dots) : indexes === null ? key : key + "[]", convertValue(el));
        });
        return false;
      }
    }
    if (isVisitable(value)) {
      return true;
    }
    formData.append(renderKey(path, key, dots), convertValue(value));
    return false;
  }
  const stack = [];
  const exposedHelpers = Object.assign(predicates, {
    defaultVisitor,
    convertValue,
    isVisitable
  });
  function build(value, path) {
    if (utils.isUndefined(value))
      return;
    if (stack.indexOf(value) !== -1) {
      throw Error("Circular reference detected in " + path.join("."));
    }
    stack.push(value);
    utils.forEach(value, function each(el, key) {
      const result = !(utils.isUndefined(el) || el === null) && visitor.call(formData, el, utils.isString(key) ? key.trim() : key, path, exposedHelpers);
      if (result === true) {
        build(el, path ? path.concat(key) : [key]);
      }
    });
    stack.pop();
  }
  if (!utils.isObject(obj)) {
    throw new TypeError("data must be an object");
  }
  build(obj);
  return formData;
}
function encode(str) {
  const charMap = {
    "!": "%21",
    "'": "%27",
    "(": "%28",
    ")": "%29",
    "~": "%7E",
    "%20": "+",
    "%00": "\0"
  };
  return encodeURIComponent(str).replace(/[!'()~]|%20|%00/g, function replacer(match) {
    return charMap[match];
  });
}
function AxiosURLSearchParams(params, options) {
  this._pairs = [];
  params && toFormData(params, this, options);
}
const prototype$1 = AxiosURLSearchParams.prototype;
prototype$1.append = function append(name, value) {
  this._pairs.push([name, value]);
};
prototype$1.toString = function toString3(encoder) {
  const _encode = encoder ? function(value) {
    return encoder.call(this, value, encode);
  } : encode;
  return this._pairs.map(function each(pair) {
    return _encode(pair[0]) + "=" + _encode(pair[1]);
  }, "").join("&");
};
function encode$1(val) {
  return encodeURIComponent(val).replace(/%3A/gi, ":").replace(/%24/g, "$").replace(/%2C/gi, ",").replace(/%20/g, "+").replace(/%5B/gi, "[").replace(/%5D/gi, "]");
}
function buildURL(url, params, options) {
  if (!params) {
    return url;
  }
  const _encode = options && options.encode || encode$1;
  const serializeFn = options && options.serialize;
  let serializedParams;
  if (serializeFn) {
    serializedParams = serializeFn(params, options);
  } else {
    serializedParams = utils.isURLSearchParams(params) ? params.toString() : new AxiosURLSearchParams(params, options).toString(_encode);
  }
  if (serializedParams) {
    const hashmarkIndex = url.indexOf("#");
    if (hashmarkIndex !== -1) {
      url = url.slice(0, hashmarkIndex);
    }
    url += (url.indexOf("?") === -1 ? "?" : "&") + serializedParams;
  }
  return url;
}
class InterceptorManager {
  constructor() {
    this.handlers = [];
  }
  use(fulfilled, rejected, options) {
    this.handlers.push({
      fulfilled,
      rejected,
      synchronous: options ? options.synchronous : false,
      runWhen: options ? options.runWhen : null
    });
    return this.handlers.length - 1;
  }
  eject(id) {
    if (this.handlers[id]) {
      this.handlers[id] = null;
    }
  }
  clear() {
    if (this.handlers) {
      this.handlers = [];
    }
  }
  forEach(fn) {
    utils.forEach(this.handlers, function forEachHandler(h) {
      if (h !== null) {
        fn(h);
      }
    });
  }
}
var transitionalDefaults = {
  silentJSONParsing: true,
  forcedJSONParsing: true,
  clarifyTimeoutError: false
};
var URLSearchParams$1 = typeof URLSearchParams !== "undefined" ? URLSearchParams : AxiosURLSearchParams;
var FormData$1 = FormData;
const isStandardBrowserEnv = (() => {
  let product;
  if (typeof navigator !== "undefined" && ((product = navigator.product) === "ReactNative" || product === "NativeScript" || product === "NS")) {
    return false;
  }
  return typeof window !== "undefined" && typeof document !== "undefined";
})();
var platform = {
  isBrowser: true,
  classes: {
    URLSearchParams: URLSearchParams$1,
    FormData: FormData$1,
    Blob
  },
  isStandardBrowserEnv,
  protocols: ["http", "https", "file", "blob", "url", "data"]
};
function toURLEncodedForm(data, options) {
  return toFormData(data, new platform.classes.URLSearchParams(), Object.assign({
    visitor: function(value, key, path, helpers) {
      return helpers.defaultVisitor.apply(this, arguments);
    }
  }, options));
}
function parsePropPath(name) {
  return utils.matchAll(/\w+|\[(\w*)]/g, name).map((match) => {
    return match[0] === "[]" ? "" : match[1] || match[0];
  });
}
function arrayToObject(arr) {
  const obj = {};
  const keys = Object.keys(arr);
  let i;
  const len = keys.length;
  let key;
  for (i = 0; i < len; i++) {
    key = keys[i];
    obj[key] = arr[key];
  }
  return obj;
}
function formDataToJSON(formData) {
  function buildPath(path, value, target, index) {
    let name = path[index++];
    const isNumericKey = Number.isFinite(+name);
    const isLast = index >= path.length;
    name = !name && utils.isArray(target) ? target.length : name;
    if (isLast) {
      if (utils.hasOwnProp(target, name)) {
        target[name] = [target[name], value];
      } else {
        target[name] = value;
      }
      return !isNumericKey;
    }
    if (!target[name] || !utils.isObject(target[name])) {
      target[name] = [];
    }
    const result = buildPath(path, value, target[name], index);
    if (result && utils.isArray(target[name])) {
      target[name] = arrayToObject(target[name]);
    }
    return !isNumericKey;
  }
  if (utils.isFormData(formData) && utils.isFunction(formData.entries)) {
    const obj = {};
    utils.forEachEntry(formData, (name, value) => {
      buildPath(parsePropPath(name), value, obj, 0);
    });
    return obj;
  }
  return null;
}
const DEFAULT_CONTENT_TYPE = {
  "Content-Type": void 0
};
function stringifySafely(rawValue, parser, encoder) {
  if (utils.isString(rawValue)) {
    try {
      (parser || JSON.parse)(rawValue);
      return utils.trim(rawValue);
    } catch (e) {
      if (e.name !== "SyntaxError") {
        throw e;
      }
    }
  }
  return (encoder || JSON.stringify)(rawValue);
}
const defaults = {
  transitional: transitionalDefaults,
  adapter: ["xhr", "http"],
  transformRequest: [function transformRequest(data, headers) {
    const contentType = headers.getContentType() || "";
    const hasJSONContentType = contentType.indexOf("application/json") > -1;
    const isObjectPayload = utils.isObject(data);
    if (isObjectPayload && utils.isHTMLForm(data)) {
      data = new FormData(data);
    }
    const isFormData2 = utils.isFormData(data);
    if (isFormData2) {
      if (!hasJSONContentType) {
        return data;
      }
      return hasJSONContentType ? JSON.stringify(formDataToJSON(data)) : data;
    }
    if (utils.isArrayBuffer(data) || utils.isBuffer(data) || utils.isStream(data) || utils.isFile(data) || utils.isBlob(data)) {
      return data;
    }
    if (utils.isArrayBufferView(data)) {
      return data.buffer;
    }
    if (utils.isURLSearchParams(data)) {
      headers.setContentType("application/x-www-form-urlencoded;charset=utf-8", false);
      return data.toString();
    }
    let isFileList2;
    if (isObjectPayload) {
      if (contentType.indexOf("application/x-www-form-urlencoded") > -1) {
        return toURLEncodedForm(data, this.formSerializer).toString();
      }
      if ((isFileList2 = utils.isFileList(data)) || contentType.indexOf("multipart/form-data") > -1) {
        const _FormData = this.env && this.env.FormData;
        return toFormData(isFileList2 ? {"files[]": data} : data, _FormData && new _FormData(), this.formSerializer);
      }
    }
    if (isObjectPayload || hasJSONContentType) {
      headers.setContentType("application/json", false);
      return stringifySafely(data);
    }
    return data;
  }],
  transformResponse: [function transformResponse(data) {
    const transitional2 = this.transitional || defaults.transitional;
    const forcedJSONParsing = transitional2 && transitional2.forcedJSONParsing;
    const JSONRequested = this.responseType === "json";
    if (data && utils.isString(data) && (forcedJSONParsing && !this.responseType || JSONRequested)) {
      const silentJSONParsing = transitional2 && transitional2.silentJSONParsing;
      const strictJSONParsing = !silentJSONParsing && JSONRequested;
      try {
        return JSON.parse(data);
      } catch (e) {
        if (strictJSONParsing) {
          if (e.name === "SyntaxError") {
            throw AxiosError.from(e, AxiosError.ERR_BAD_RESPONSE, this, null, this.response);
          }
          throw e;
        }
      }
    }
    return data;
  }],
  timeout: 0,
  xsrfCookieName: "XSRF-TOKEN",
  xsrfHeaderName: "X-XSRF-TOKEN",
  maxContentLength: -1,
  maxBodyLength: -1,
  env: {
    FormData: platform.classes.FormData,
    Blob: platform.classes.Blob
  },
  validateStatus: function validateStatus(status) {
    return status >= 200 && status < 300;
  },
  headers: {
    common: {
      Accept: "application/json, text/plain, */*"
    }
  }
};
utils.forEach(["delete", "get", "head"], function forEachMethodNoData(method) {
  defaults.headers[method] = {};
});
utils.forEach(["post", "put", "patch"], function forEachMethodWithData(method) {
  defaults.headers[method] = utils.merge(DEFAULT_CONTENT_TYPE);
});
const ignoreDuplicateOf = utils.toObjectSet([
  "age",
  "authorization",
  "content-length",
  "content-type",
  "etag",
  "expires",
  "from",
  "host",
  "if-modified-since",
  "if-unmodified-since",
  "last-modified",
  "location",
  "max-forwards",
  "proxy-authorization",
  "referer",
  "retry-after",
  "user-agent"
]);
var parseHeaders = (rawHeaders) => {
  const parsed = {};
  let key;
  let val;
  let i;
  rawHeaders && rawHeaders.split("\n").forEach(function parser(line) {
    i = line.indexOf(":");
    key = line.substring(0, i).trim().toLowerCase();
    val = line.substring(i + 1).trim();
    if (!key || parsed[key] && ignoreDuplicateOf[key]) {
      return;
    }
    if (key === "set-cookie") {
      if (parsed[key]) {
        parsed[key].push(val);
      } else {
        parsed[key] = [val];
      }
    } else {
      parsed[key] = parsed[key] ? parsed[key] + ", " + val : val;
    }
  });
  return parsed;
};
const $internals = Symbol("internals");
function normalizeHeader(header) {
  return header && String(header).trim().toLowerCase();
}
function normalizeValue(value) {
  if (value === false || value == null) {
    return value;
  }
  return utils.isArray(value) ? value.map(normalizeValue) : String(value);
}
function parseTokens(str) {
  const tokens = Object.create(null);
  const tokensRE = /([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;
  let match;
  while (match = tokensRE.exec(str)) {
    tokens[match[1]] = match[2];
  }
  return tokens;
}
function isValidHeaderName(str) {
  return /^[-_a-zA-Z]+$/.test(str.trim());
}
function matchHeaderValue(context, value, header, filter2) {
  if (utils.isFunction(filter2)) {
    return filter2.call(this, value, header);
  }
  if (!utils.isString(value))
    return;
  if (utils.isString(filter2)) {
    return value.indexOf(filter2) !== -1;
  }
  if (utils.isRegExp(filter2)) {
    return filter2.test(value);
  }
}
function formatHeader(header) {
  return header.trim().toLowerCase().replace(/([a-z\d])(\w*)/g, (w, char, str) => {
    return char.toUpperCase() + str;
  });
}
function buildAccessors(obj, header) {
  const accessorName = utils.toCamelCase(" " + header);
  ["get", "set", "has"].forEach((methodName) => {
    Object.defineProperty(obj, methodName + accessorName, {
      value: function(arg1, arg2, arg3) {
        return this[methodName].call(this, header, arg1, arg2, arg3);
      },
      configurable: true
    });
  });
}
class AxiosHeaders {
  constructor(headers) {
    headers && this.set(headers);
  }
  set(header, valueOrRewrite, rewrite) {
    const self2 = this;
    function setHeader(_value, _header, _rewrite) {
      const lHeader = normalizeHeader(_header);
      if (!lHeader) {
        throw new Error("header name must be a non-empty string");
      }
      const key = utils.findKey(self2, lHeader);
      if (!key || self2[key] === void 0 || _rewrite === true || _rewrite === void 0 && self2[key] !== false) {
        self2[key || _header] = normalizeValue(_value);
      }
    }
    const setHeaders = (headers, _rewrite) => utils.forEach(headers, (_value, _header) => setHeader(_value, _header, _rewrite));
    if (utils.isPlainObject(header) || header instanceof this.constructor) {
      setHeaders(header, valueOrRewrite);
    } else if (utils.isString(header) && (header = header.trim()) && !isValidHeaderName(header)) {
      setHeaders(parseHeaders(header), valueOrRewrite);
    } else {
      header != null && setHeader(valueOrRewrite, header, rewrite);
    }
    return this;
  }
  get(header, parser) {
    header = normalizeHeader(header);
    if (header) {
      const key = utils.findKey(this, header);
      if (key) {
        const value = this[key];
        if (!parser) {
          return value;
        }
        if (parser === true) {
          return parseTokens(value);
        }
        if (utils.isFunction(parser)) {
          return parser.call(this, value, key);
        }
        if (utils.isRegExp(parser)) {
          return parser.exec(value);
        }
        throw new TypeError("parser must be boolean|regexp|function");
      }
    }
  }
  has(header, matcher) {
    header = normalizeHeader(header);
    if (header) {
      const key = utils.findKey(this, header);
      return !!(key && (!matcher || matchHeaderValue(this, this[key], key, matcher)));
    }
    return false;
  }
  delete(header, matcher) {
    const self2 = this;
    let deleted = false;
    function deleteHeader(_header) {
      _header = normalizeHeader(_header);
      if (_header) {
        const key = utils.findKey(self2, _header);
        if (key && (!matcher || matchHeaderValue(self2, self2[key], key, matcher))) {
          delete self2[key];
          deleted = true;
        }
      }
    }
    if (utils.isArray(header)) {
      header.forEach(deleteHeader);
    } else {
      deleteHeader(header);
    }
    return deleted;
  }
  clear() {
    return Object.keys(this).forEach(this.delete.bind(this));
  }
  normalize(format) {
    const self2 = this;
    const headers = {};
    utils.forEach(this, (value, header) => {
      const key = utils.findKey(headers, header);
      if (key) {
        self2[key] = normalizeValue(value);
        delete self2[header];
        return;
      }
      const normalized = format ? formatHeader(header) : String(header).trim();
      if (normalized !== header) {
        delete self2[header];
      }
      self2[normalized] = normalizeValue(value);
      headers[normalized] = true;
    });
    return this;
  }
  concat(...targets) {
    return this.constructor.concat(this, ...targets);
  }
  toJSON(asStrings) {
    const obj = Object.create(null);
    utils.forEach(this, (value, header) => {
      value != null && value !== false && (obj[header] = asStrings && utils.isArray(value) ? value.join(", ") : value);
    });
    return obj;
  }
  [Symbol.iterator]() {
    return Object.entries(this.toJSON())[Symbol.iterator]();
  }
  toString() {
    return Object.entries(this.toJSON()).map(([header, value]) => header + ": " + value).join("\n");
  }
  get [Symbol.toStringTag]() {
    return "AxiosHeaders";
  }
  static from(thing) {
    return thing instanceof this ? thing : new this(thing);
  }
  static concat(first, ...targets) {
    const computed = new this(first);
    targets.forEach((target) => computed.set(target));
    return computed;
  }
  static accessor(header) {
    const internals = this[$internals] = this[$internals] = {
      accessors: {}
    };
    const accessors = internals.accessors;
    const prototype2 = this.prototype;
    function defineAccessor(_header) {
      const lHeader = normalizeHeader(_header);
      if (!accessors[lHeader]) {
        buildAccessors(prototype2, _header);
        accessors[lHeader] = true;
      }
    }
    utils.isArray(header) ? header.forEach(defineAccessor) : defineAccessor(header);
    return this;
  }
}
AxiosHeaders.accessor(["Content-Type", "Content-Length", "Accept", "Accept-Encoding", "User-Agent"]);
utils.freezeMethods(AxiosHeaders.prototype);
utils.freezeMethods(AxiosHeaders);
function transformData(fns, response) {
  const config = this || defaults;
  const context = response || config;
  const headers = AxiosHeaders.from(context.headers);
  let data = context.data;
  utils.forEach(fns, function transform(fn) {
    data = fn.call(config, data, headers.normalize(), response ? response.status : void 0);
  });
  headers.normalize();
  return data;
}
function isCancel(value) {
  return !!(value && value.__CANCEL__);
}
function CanceledError(message, config, request) {
  AxiosError.call(this, message == null ? "canceled" : message, AxiosError.ERR_CANCELED, config, request);
  this.name = "CanceledError";
}
utils.inherits(CanceledError, AxiosError, {
  __CANCEL__: true
});
var httpAdapter = null;
function settle(resolve, reject, response) {
  const validateStatus2 = response.config.validateStatus;
  if (!response.status || !validateStatus2 || validateStatus2(response.status)) {
    resolve(response);
  } else {
    reject(new AxiosError("Request failed with status code " + response.status, [AxiosError.ERR_BAD_REQUEST, AxiosError.ERR_BAD_RESPONSE][Math.floor(response.status / 100) - 4], response.config, response.request, response));
  }
}
var cookies = platform.isStandardBrowserEnv ? function standardBrowserEnv() {
  return {
    write: function write3(name, value, expires, path, domain, secure) {
      const cookie = [];
      cookie.push(name + "=" + encodeURIComponent(value));
      if (utils.isNumber(expires)) {
        cookie.push("expires=" + new Date(expires).toGMTString());
      }
      if (utils.isString(path)) {
        cookie.push("path=" + path);
      }
      if (utils.isString(domain)) {
        cookie.push("domain=" + domain);
      }
      if (secure === true) {
        cookie.push("secure");
      }
      document.cookie = cookie.join("; ");
    },
    read: function read2(name) {
      const match = document.cookie.match(new RegExp("(^|;\\s*)(" + name + ")=([^;]*)"));
      return match ? decodeURIComponent(match[3]) : null;
    },
    remove: function remove(name) {
      this.write(name, "", Date.now() - 864e5);
    }
  };
}() : function nonStandardBrowserEnv() {
  return {
    write: function write3() {
    },
    read: function read2() {
      return null;
    },
    remove: function remove() {
    }
  };
}();
function isAbsoluteURL(url) {
  return /^([a-z][a-z\d+\-.]*:)?\/\//i.test(url);
}
function combineURLs(baseURL, relativeURL) {
  return relativeURL ? baseURL.replace(/\/+$/, "") + "/" + relativeURL.replace(/^\/+/, "") : baseURL;
}
function buildFullPath(baseURL, requestedURL) {
  if (baseURL && !isAbsoluteURL(requestedURL)) {
    return combineURLs(baseURL, requestedURL);
  }
  return requestedURL;
}
var isURLSameOrigin = platform.isStandardBrowserEnv ? function standardBrowserEnv2() {
  const msie = /(msie|trident)/i.test(navigator.userAgent);
  const urlParsingNode = document.createElement("a");
  let originURL;
  function resolveURL(url) {
    let href = url;
    if (msie) {
      urlParsingNode.setAttribute("href", href);
      href = urlParsingNode.href;
    }
    urlParsingNode.setAttribute("href", href);
    return {
      href: urlParsingNode.href,
      protocol: urlParsingNode.protocol ? urlParsingNode.protocol.replace(/:$/, "") : "",
      host: urlParsingNode.host,
      search: urlParsingNode.search ? urlParsingNode.search.replace(/^\?/, "") : "",
      hash: urlParsingNode.hash ? urlParsingNode.hash.replace(/^#/, "") : "",
      hostname: urlParsingNode.hostname,
      port: urlParsingNode.port,
      pathname: urlParsingNode.pathname.charAt(0) === "/" ? urlParsingNode.pathname : "/" + urlParsingNode.pathname
    };
  }
  originURL = resolveURL(window.location.href);
  return function isURLSameOrigin2(requestURL) {
    const parsed = utils.isString(requestURL) ? resolveURL(requestURL) : requestURL;
    return parsed.protocol === originURL.protocol && parsed.host === originURL.host;
  };
}() : function nonStandardBrowserEnv2() {
  return function isURLSameOrigin2() {
    return true;
  };
}();
function parseProtocol(url) {
  const match = /^([-+\w]{1,25})(:?\/\/|:)/.exec(url);
  return match && match[1] || "";
}
function speedometer(samplesCount, min) {
  samplesCount = samplesCount || 10;
  const bytes = new Array(samplesCount);
  const timestamps = new Array(samplesCount);
  let head = 0;
  let tail = 0;
  let firstSampleTS;
  min = min !== void 0 ? min : 1e3;
  return function push(chunkLength) {
    const now = Date.now();
    const startedAt = timestamps[tail];
    if (!firstSampleTS) {
      firstSampleTS = now;
    }
    bytes[head] = chunkLength;
    timestamps[head] = now;
    let i = tail;
    let bytesCount = 0;
    while (i !== head) {
      bytesCount += bytes[i++];
      i = i % samplesCount;
    }
    head = (head + 1) % samplesCount;
    if (head === tail) {
      tail = (tail + 1) % samplesCount;
    }
    if (now - firstSampleTS < min) {
      return;
    }
    const passed = startedAt && now - startedAt;
    return passed ? Math.round(bytesCount * 1e3 / passed) : void 0;
  };
}
function progressEventReducer(listener, isDownloadStream) {
  let bytesNotified = 0;
  const _speedometer = speedometer(50, 250);
  return (e) => {
    const loaded = e.loaded;
    const total = e.lengthComputable ? e.total : void 0;
    const progressBytes = loaded - bytesNotified;
    const rate = _speedometer(progressBytes);
    const inRange = loaded <= total;
    bytesNotified = loaded;
    const data = {
      loaded,
      total,
      progress: total ? loaded / total : void 0,
      bytes: progressBytes,
      rate: rate ? rate : void 0,
      estimated: rate && total && inRange ? (total - loaded) / rate : void 0,
      event: e
    };
    data[isDownloadStream ? "download" : "upload"] = true;
    listener(data);
  };
}
const isXHRAdapterSupported = typeof XMLHttpRequest !== "undefined";
var xhrAdapter = isXHRAdapterSupported && function(config) {
  return new Promise(function dispatchXhrRequest(resolve, reject) {
    let requestData = config.data;
    const requestHeaders = AxiosHeaders.from(config.headers).normalize();
    const responseType = config.responseType;
    let onCanceled;
    function done() {
      if (config.cancelToken) {
        config.cancelToken.unsubscribe(onCanceled);
      }
      if (config.signal) {
        config.signal.removeEventListener("abort", onCanceled);
      }
    }
    if (utils.isFormData(requestData) && platform.isStandardBrowserEnv) {
      requestHeaders.setContentType(false);
    }
    let request = new XMLHttpRequest();
    if (config.auth) {
      const username = config.auth.username || "";
      const password = config.auth.password ? unescape(encodeURIComponent(config.auth.password)) : "";
      requestHeaders.set("Authorization", "Basic " + btoa(username + ":" + password));
    }
    const fullPath = buildFullPath(config.baseURL, config.url);
    request.open(config.method.toUpperCase(), buildURL(fullPath, config.params, config.paramsSerializer), true);
    request.timeout = config.timeout;
    function onloadend() {
      if (!request) {
        return;
      }
      const responseHeaders = AxiosHeaders.from("getAllResponseHeaders" in request && request.getAllResponseHeaders());
      const responseData = !responseType || responseType === "text" || responseType === "json" ? request.responseText : request.response;
      const response = {
        data: responseData,
        status: request.status,
        statusText: request.statusText,
        headers: responseHeaders,
        config,
        request
      };
      settle(function _resolve(value) {
        resolve(value);
        done();
      }, function _reject(err) {
        reject(err);
        done();
      }, response);
      request = null;
    }
    if ("onloadend" in request) {
      request.onloadend = onloadend;
    } else {
      request.onreadystatechange = function handleLoad() {
        if (!request || request.readyState !== 4) {
          return;
        }
        if (request.status === 0 && !(request.responseURL && request.responseURL.indexOf("file:") === 0)) {
          return;
        }
        setTimeout(onloadend);
      };
    }
    request.onabort = function handleAbort() {
      if (!request) {
        return;
      }
      reject(new AxiosError("Request aborted", AxiosError.ECONNABORTED, config, request));
      request = null;
    };
    request.onerror = function handleError() {
      reject(new AxiosError("Network Error", AxiosError.ERR_NETWORK, config, request));
      request = null;
    };
    request.ontimeout = function handleTimeout() {
      let timeoutErrorMessage = config.timeout ? "timeout of " + config.timeout + "ms exceeded" : "timeout exceeded";
      const transitional2 = config.transitional || transitionalDefaults;
      if (config.timeoutErrorMessage) {
        timeoutErrorMessage = config.timeoutErrorMessage;
      }
      reject(new AxiosError(timeoutErrorMessage, transitional2.clarifyTimeoutError ? AxiosError.ETIMEDOUT : AxiosError.ECONNABORTED, config, request));
      request = null;
    };
    if (platform.isStandardBrowserEnv) {
      const xsrfValue = (config.withCredentials || isURLSameOrigin(fullPath)) && config.xsrfCookieName && cookies.read(config.xsrfCookieName);
      if (xsrfValue) {
        requestHeaders.set(config.xsrfHeaderName, xsrfValue);
      }
    }
    requestData === void 0 && requestHeaders.setContentType(null);
    if ("setRequestHeader" in request) {
      utils.forEach(requestHeaders.toJSON(), function setRequestHeader(val, key) {
        request.setRequestHeader(key, val);
      });
    }
    if (!utils.isUndefined(config.withCredentials)) {
      request.withCredentials = !!config.withCredentials;
    }
    if (responseType && responseType !== "json") {
      request.responseType = config.responseType;
    }
    if (typeof config.onDownloadProgress === "function") {
      request.addEventListener("progress", progressEventReducer(config.onDownloadProgress, true));
    }
    if (typeof config.onUploadProgress === "function" && request.upload) {
      request.upload.addEventListener("progress", progressEventReducer(config.onUploadProgress));
    }
    if (config.cancelToken || config.signal) {
      onCanceled = (cancel) => {
        if (!request) {
          return;
        }
        reject(!cancel || cancel.type ? new CanceledError(null, config, request) : cancel);
        request.abort();
        request = null;
      };
      config.cancelToken && config.cancelToken.subscribe(onCanceled);
      if (config.signal) {
        config.signal.aborted ? onCanceled() : config.signal.addEventListener("abort", onCanceled);
      }
    }
    const protocol = parseProtocol(fullPath);
    if (protocol && platform.protocols.indexOf(protocol) === -1) {
      reject(new AxiosError("Unsupported protocol " + protocol + ":", AxiosError.ERR_BAD_REQUEST, config));
      return;
    }
    request.send(requestData || null);
  });
};
const knownAdapters = {
  http: httpAdapter,
  xhr: xhrAdapter
};
utils.forEach(knownAdapters, (fn, value) => {
  if (fn) {
    try {
      Object.defineProperty(fn, "name", {value});
    } catch (e) {
    }
    Object.defineProperty(fn, "adapterName", {value});
  }
});
var adapters = {
  getAdapter: (adapters2) => {
    adapters2 = utils.isArray(adapters2) ? adapters2 : [adapters2];
    const {length} = adapters2;
    let nameOrAdapter;
    let adapter;
    for (let i = 0; i < length; i++) {
      nameOrAdapter = adapters2[i];
      if (adapter = utils.isString(nameOrAdapter) ? knownAdapters[nameOrAdapter.toLowerCase()] : nameOrAdapter) {
        break;
      }
    }
    if (!adapter) {
      if (adapter === false) {
        throw new AxiosError(`Adapter ${nameOrAdapter} is not supported by the environment`, "ERR_NOT_SUPPORT");
      }
      throw new Error(utils.hasOwnProp(knownAdapters, nameOrAdapter) ? `Adapter '${nameOrAdapter}' is not available in the build` : `Unknown adapter '${nameOrAdapter}'`);
    }
    if (!utils.isFunction(adapter)) {
      throw new TypeError("adapter is not a function");
    }
    return adapter;
  },
  adapters: knownAdapters
};
function throwIfCancellationRequested(config) {
  if (config.cancelToken) {
    config.cancelToken.throwIfRequested();
  }
  if (config.signal && config.signal.aborted) {
    throw new CanceledError();
  }
}
function dispatchRequest(config) {
  throwIfCancellationRequested(config);
  config.headers = AxiosHeaders.from(config.headers);
  config.data = transformData.call(config, config.transformRequest);
  if (["post", "put", "patch"].indexOf(config.method) !== -1) {
    config.headers.setContentType("application/x-www-form-urlencoded", false);
  }
  const adapter = adapters.getAdapter(config.adapter || defaults.adapter);
  return adapter(config).then(function onAdapterResolution(response) {
    throwIfCancellationRequested(config);
    response.data = transformData.call(config, config.transformResponse, response);
    response.headers = AxiosHeaders.from(response.headers);
    return response;
  }, function onAdapterRejection(reason) {
    if (!isCancel(reason)) {
      throwIfCancellationRequested(config);
      if (reason && reason.response) {
        reason.response.data = transformData.call(config, config.transformResponse, reason.response);
        reason.response.headers = AxiosHeaders.from(reason.response.headers);
      }
    }
    return Promise.reject(reason);
  });
}
const headersToObject = (thing) => thing instanceof AxiosHeaders ? thing.toJSON() : thing;
function mergeConfig(config1, config2) {
  config2 = config2 || {};
  const config = {};
  function getMergedValue(target, source, caseless) {
    if (utils.isPlainObject(target) && utils.isPlainObject(source)) {
      return utils.merge.call({caseless}, target, source);
    } else if (utils.isPlainObject(source)) {
      return utils.merge({}, source);
    } else if (utils.isArray(source)) {
      return source.slice();
    }
    return source;
  }
  function mergeDeepProperties(a, b, caseless) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(a, b, caseless);
    } else if (!utils.isUndefined(a)) {
      return getMergedValue(void 0, a, caseless);
    }
  }
  function valueFromConfig2(a, b) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(void 0, b);
    }
  }
  function defaultToConfig2(a, b) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(void 0, b);
    } else if (!utils.isUndefined(a)) {
      return getMergedValue(void 0, a);
    }
  }
  function mergeDirectKeys(a, b, prop) {
    if (prop in config2) {
      return getMergedValue(a, b);
    } else if (prop in config1) {
      return getMergedValue(void 0, a);
    }
  }
  const mergeMap = {
    url: valueFromConfig2,
    method: valueFromConfig2,
    data: valueFromConfig2,
    baseURL: defaultToConfig2,
    transformRequest: defaultToConfig2,
    transformResponse: defaultToConfig2,
    paramsSerializer: defaultToConfig2,
    timeout: defaultToConfig2,
    timeoutMessage: defaultToConfig2,
    withCredentials: defaultToConfig2,
    adapter: defaultToConfig2,
    responseType: defaultToConfig2,
    xsrfCookieName: defaultToConfig2,
    xsrfHeaderName: defaultToConfig2,
    onUploadProgress: defaultToConfig2,
    onDownloadProgress: defaultToConfig2,
    decompress: defaultToConfig2,
    maxContentLength: defaultToConfig2,
    maxBodyLength: defaultToConfig2,
    beforeRedirect: defaultToConfig2,
    transport: defaultToConfig2,
    httpAgent: defaultToConfig2,
    httpsAgent: defaultToConfig2,
    cancelToken: defaultToConfig2,
    socketPath: defaultToConfig2,
    responseEncoding: defaultToConfig2,
    validateStatus: mergeDirectKeys,
    headers: (a, b) => mergeDeepProperties(headersToObject(a), headersToObject(b), true)
  };
  utils.forEach(Object.keys(config1).concat(Object.keys(config2)), function computeConfigValue(prop) {
    const merge2 = mergeMap[prop] || mergeDeepProperties;
    const configValue = merge2(config1[prop], config2[prop], prop);
    utils.isUndefined(configValue) && merge2 !== mergeDirectKeys || (config[prop] = configValue);
  });
  return config;
}
const VERSION = "1.2.0";
const validators = {};
["object", "boolean", "number", "function", "string", "symbol"].forEach((type, i) => {
  validators[type] = function validator2(thing) {
    return typeof thing === type || "a" + (i < 1 ? "n " : " ") + type;
  };
});
const deprecatedWarnings = {};
validators.transitional = function transitional(validator2, version, message) {
  function formatMessage(opt, desc) {
    return "[Axios v" + VERSION + "] Transitional option '" + opt + "'" + desc + (message ? ". " + message : "");
  }
  return (value, opt, opts) => {
    if (validator2 === false) {
      throw new AxiosError(formatMessage(opt, " has been removed" + (version ? " in " + version : "")), AxiosError.ERR_DEPRECATED);
    }
    if (version && !deprecatedWarnings[opt]) {
      deprecatedWarnings[opt] = true;
      console.warn(formatMessage(opt, " has been deprecated since v" + version + " and will be removed in the near future"));
    }
    return validator2 ? validator2(value, opt, opts) : true;
  };
};
function assertOptions(options, schema, allowUnknown) {
  if (typeof options !== "object") {
    throw new AxiosError("options must be an object", AxiosError.ERR_BAD_OPTION_VALUE);
  }
  const keys = Object.keys(options);
  let i = keys.length;
  while (i-- > 0) {
    const opt = keys[i];
    const validator2 = schema[opt];
    if (validator2) {
      const value = options[opt];
      const result = value === void 0 || validator2(value, opt, options);
      if (result !== true) {
        throw new AxiosError("option " + opt + " must be " + result, AxiosError.ERR_BAD_OPTION_VALUE);
      }
      continue;
    }
    if (allowUnknown !== true) {
      throw new AxiosError("Unknown option " + opt, AxiosError.ERR_BAD_OPTION);
    }
  }
}
var validator = {
  assertOptions,
  validators
};
const validators$1 = validator.validators;
class Axios {
  constructor(instanceConfig) {
    this.defaults = instanceConfig;
    this.interceptors = {
      request: new InterceptorManager(),
      response: new InterceptorManager()
    };
  }
  request(configOrUrl, config) {
    if (typeof configOrUrl === "string") {
      config = config || {};
      config.url = configOrUrl;
    } else {
      config = configOrUrl || {};
    }
    config = mergeConfig(this.defaults, config);
    const {transitional: transitional2, paramsSerializer, headers} = config;
    if (transitional2 !== void 0) {
      validator.assertOptions(transitional2, {
        silentJSONParsing: validators$1.transitional(validators$1.boolean),
        forcedJSONParsing: validators$1.transitional(validators$1.boolean),
        clarifyTimeoutError: validators$1.transitional(validators$1.boolean)
      }, false);
    }
    if (paramsSerializer !== void 0) {
      validator.assertOptions(paramsSerializer, {
        encode: validators$1.function,
        serialize: validators$1.function
      }, true);
    }
    config.method = (config.method || this.defaults.method || "get").toLowerCase();
    let contextHeaders;
    contextHeaders = headers && utils.merge(headers.common, headers[config.method]);
    contextHeaders && utils.forEach(["delete", "get", "head", "post", "put", "patch", "common"], (method) => {
      delete headers[method];
    });
    config.headers = AxiosHeaders.concat(contextHeaders, headers);
    const requestInterceptorChain = [];
    let synchronousRequestInterceptors = true;
    this.interceptors.request.forEach(function unshiftRequestInterceptors(interceptor) {
      if (typeof interceptor.runWhen === "function" && interceptor.runWhen(config) === false) {
        return;
      }
      synchronousRequestInterceptors = synchronousRequestInterceptors && interceptor.synchronous;
      requestInterceptorChain.unshift(interceptor.fulfilled, interceptor.rejected);
    });
    const responseInterceptorChain = [];
    this.interceptors.response.forEach(function pushResponseInterceptors(interceptor) {
      responseInterceptorChain.push(interceptor.fulfilled, interceptor.rejected);
    });
    let promise;
    let i = 0;
    let len;
    if (!synchronousRequestInterceptors) {
      const chain = [dispatchRequest.bind(this), void 0];
      chain.unshift.apply(chain, requestInterceptorChain);
      chain.push.apply(chain, responseInterceptorChain);
      len = chain.length;
      promise = Promise.resolve(config);
      while (i < len) {
        promise = promise.then(chain[i++], chain[i++]);
      }
      return promise;
    }
    len = requestInterceptorChain.length;
    let newConfig = config;
    i = 0;
    while (i < len) {
      const onFulfilled = requestInterceptorChain[i++];
      const onRejected = requestInterceptorChain[i++];
      try {
        newConfig = onFulfilled(newConfig);
      } catch (error) {
        onRejected.call(this, error);
        break;
      }
    }
    try {
      promise = dispatchRequest.call(this, newConfig);
    } catch (error) {
      return Promise.reject(error);
    }
    i = 0;
    len = responseInterceptorChain.length;
    while (i < len) {
      promise = promise.then(responseInterceptorChain[i++], responseInterceptorChain[i++]);
    }
    return promise;
  }
  getUri(config) {
    config = mergeConfig(this.defaults, config);
    const fullPath = buildFullPath(config.baseURL, config.url);
    return buildURL(fullPath, config.params, config.paramsSerializer);
  }
}
utils.forEach(["delete", "get", "head", "options"], function forEachMethodNoData2(method) {
  Axios.prototype[method] = function(url, config) {
    return this.request(mergeConfig(config || {}, {
      method,
      url,
      data: (config || {}).data
    }));
  };
});
utils.forEach(["post", "put", "patch"], function forEachMethodWithData2(method) {
  function generateHTTPMethod(isForm) {
    return function httpMethod(url, data, config) {
      return this.request(mergeConfig(config || {}, {
        method,
        headers: isForm ? {
          "Content-Type": "multipart/form-data"
        } : {},
        url,
        data
      }));
    };
  }
  Axios.prototype[method] = generateHTTPMethod();
  Axios.prototype[method + "Form"] = generateHTTPMethod(true);
});
class CancelToken {
  constructor(executor) {
    if (typeof executor !== "function") {
      throw new TypeError("executor must be a function.");
    }
    let resolvePromise;
    this.promise = new Promise(function promiseExecutor(resolve) {
      resolvePromise = resolve;
    });
    const token = this;
    this.promise.then((cancel) => {
      if (!token._listeners)
        return;
      let i = token._listeners.length;
      while (i-- > 0) {
        token._listeners[i](cancel);
      }
      token._listeners = null;
    });
    this.promise.then = (onfulfilled) => {
      let _resolve;
      const promise = new Promise((resolve) => {
        token.subscribe(resolve);
        _resolve = resolve;
      }).then(onfulfilled);
      promise.cancel = function reject() {
        token.unsubscribe(_resolve);
      };
      return promise;
    };
    executor(function cancel(message, config, request) {
      if (token.reason) {
        return;
      }
      token.reason = new CanceledError(message, config, request);
      resolvePromise(token.reason);
    });
  }
  throwIfRequested() {
    if (this.reason) {
      throw this.reason;
    }
  }
  subscribe(listener) {
    if (this.reason) {
      listener(this.reason);
      return;
    }
    if (this._listeners) {
      this._listeners.push(listener);
    } else {
      this._listeners = [listener];
    }
  }
  unsubscribe(listener) {
    if (!this._listeners) {
      return;
    }
    const index = this._listeners.indexOf(listener);
    if (index !== -1) {
      this._listeners.splice(index, 1);
    }
  }
  static source() {
    let cancel;
    const token = new CancelToken(function executor(c) {
      cancel = c;
    });
    return {
      token,
      cancel
    };
  }
}
function spread(callback) {
  return function wrap(arr) {
    return callback.apply(null, arr);
  };
}
function isAxiosError(payload) {
  return utils.isObject(payload) && payload.isAxiosError === true;
}
function createInstance(defaultConfig) {
  const context = new Axios(defaultConfig);
  const instance = bind(Axios.prototype.request, context);
  utils.extend(instance, Axios.prototype, context, {allOwnKeys: true});
  utils.extend(instance, context, null, {allOwnKeys: true});
  instance.create = function create(instanceConfig) {
    return createInstance(mergeConfig(defaultConfig, instanceConfig));
  };
  return instance;
}
const axios = createInstance(defaults);
axios.Axios = Axios;
axios.CanceledError = CanceledError;
axios.CancelToken = CancelToken;
axios.isCancel = isCancel;
axios.VERSION = VERSION;
axios.toFormData = toFormData;
axios.AxiosError = AxiosError;
axios.Cancel = axios.CanceledError;
axios.all = function all(promises) {
  return Promise.all(promises);
};
axios.spread = spread;
axios.isAxiosError = isAxiosError;
axios.AxiosHeaders = AxiosHeaders;
axios.formToJSON = (thing) => formDataToJSON(utils.isHTMLForm(thing) ? new FormData(thing) : thing);
axios.default = axios;

var global$1$1 = typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {};
var freeGlobal = typeof global$1$1 == "object" && global$1$1 && global$1$1.Object === Object && global$1$1;
var freeSelf = typeof self == "object" && self && self.Object === Object && self;
var root = freeGlobal || freeSelf || Function("return this")();
var Symbol$1 = root.Symbol;
var objectProto = Object.prototype;
var hasOwnProperty$1 = objectProto.hasOwnProperty;
var nativeObjectToString = objectProto.toString;
var symToStringTag = Symbol$1 ? Symbol$1.toStringTag : void 0;
function getRawTag(value) {
  var isOwn = hasOwnProperty$1.call(value, symToStringTag), tag = value[symToStringTag];
  try {
    value[symToStringTag] = void 0;
    var unmasked = true;
  } catch (e) {
  }
  var result2 = nativeObjectToString.call(value);
  if (unmasked) {
    if (isOwn) {
      value[symToStringTag] = tag;
    } else {
      delete value[symToStringTag];
    }
  }
  return result2;
}
var objectProto$1 = Object.prototype;
var nativeObjectToString$1 = objectProto$1.toString;
function objectToString(value) {
  return nativeObjectToString$1.call(value);
}
var nullTag = "[object Null]", undefinedTag = "[object Undefined]";
var symToStringTag$1 = Symbol$1 ? Symbol$1.toStringTag : void 0;
function baseGetTag(value) {
  if (value == null) {
    return value === void 0 ? undefinedTag : nullTag;
  }
  return symToStringTag$1 && symToStringTag$1 in Object(value) ? getRawTag(value) : objectToString(value);
}
function isObjectLike(value) {
  return value != null && typeof value == "object";
}
var symbolTag = "[object Symbol]";
function isSymbol(value) {
  return typeof value == "symbol" || isObjectLike(value) && baseGetTag(value) == symbolTag;
}
var NAN = 0 / 0;
function baseToNumber(value) {
  if (typeof value == "number") {
    return value;
  }
  if (isSymbol(value)) {
    return NAN;
  }
  return +value;
}
function arrayMap(array2, iteratee2) {
  var index = -1, length = array2 == null ? 0 : array2.length, result2 = Array(length);
  while (++index < length) {
    result2[index] = iteratee2(array2[index], index, array2);
  }
  return result2;
}
var isArray$2 = Array.isArray;
var INFINITY = 1 / 0;
var symbolProto = Symbol$1 ? Symbol$1.prototype : void 0, symbolToString = symbolProto ? symbolProto.toString : void 0;
function baseToString(value) {
  if (typeof value == "string") {
    return value;
  }
  if (isArray$2(value)) {
    return arrayMap(value, baseToString) + "";
  }
  if (isSymbol(value)) {
    return symbolToString ? symbolToString.call(value) : "";
  }
  var result2 = value + "";
  return result2 == "0" && 1 / value == -INFINITY ? "-0" : result2;
}
function createMathOperation(operator, defaultValue) {
  return function(value, other) {
    var result2;
    if (value === void 0 && other === void 0) {
      return defaultValue;
    }
    if (value !== void 0) {
      result2 = value;
    }
    if (other !== void 0) {
      if (result2 === void 0) {
        return other;
      }
      if (typeof value == "string" || typeof other == "string") {
        value = baseToString(value);
        other = baseToString(other);
      } else {
        value = baseToNumber(value);
        other = baseToNumber(other);
      }
      result2 = operator(value, other);
    }
    return result2;
  };
}
var add = createMathOperation(function(augend, addend) {
  return augend + addend;
}, 0);
var reWhitespace = /\s/;
function trimmedEndIndex(string2) {
  var index = string2.length;
  while (index-- && reWhitespace.test(string2.charAt(index))) {
  }
  return index;
}
var reTrimStart = /^\s+/;
function baseTrim(string2) {
  return string2 ? string2.slice(0, trimmedEndIndex(string2) + 1).replace(reTrimStart, "") : string2;
}
function isObject$1(value) {
  var type = typeof value;
  return value != null && (type == "object" || type == "function");
}
var NAN$1 = 0 / 0;
var reIsBadHex = /^[-+]0x[0-9a-f]+$/i;
var reIsBinary = /^0b[01]+$/i;
var reIsOctal = /^0o[0-7]+$/i;
var freeParseInt = parseInt;
function toNumber(value) {
  if (typeof value == "number") {
    return value;
  }
  if (isSymbol(value)) {
    return NAN$1;
  }
  if (isObject$1(value)) {
    var other = typeof value.valueOf == "function" ? value.valueOf() : value;
    value = isObject$1(other) ? other + "" : other;
  }
  if (typeof value != "string") {
    return value === 0 ? value : +value;
  }
  value = baseTrim(value);
  var isBinary = reIsBinary.test(value);
  return isBinary || reIsOctal.test(value) ? freeParseInt(value.slice(2), isBinary ? 2 : 8) : reIsBadHex.test(value) ? NAN$1 : +value;
}
var INFINITY$1 = 1 / 0, MAX_INTEGER = 17976931348623157e292;
function toFinite(value) {
  if (!value) {
    return value === 0 ? value : 0;
  }
  value = toNumber(value);
  if (value === INFINITY$1 || value === -INFINITY$1) {
    var sign = value < 0 ? -1 : 1;
    return sign * MAX_INTEGER;
  }
  return value === value ? value : 0;
}
function toInteger(value) {
  var result2 = toFinite(value), remainder = result2 % 1;
  return result2 === result2 ? remainder ? result2 - remainder : result2 : 0;
}
var FUNC_ERROR_TEXT = "Expected a function";
function after(n, func2) {
  if (typeof func2 != "function") {
    throw new TypeError(FUNC_ERROR_TEXT);
  }
  n = toInteger(n);
  return function() {
    if (--n < 1) {
      return func2.apply(this, arguments);
    }
  };
}
function identity$1(value) {
  return value;
}
var asyncTag = "[object AsyncFunction]", funcTag = "[object Function]", genTag = "[object GeneratorFunction]", proxyTag = "[object Proxy]";
function isFunction$1(value) {
  if (!isObject$1(value)) {
    return false;
  }
  var tag = baseGetTag(value);
  return tag == funcTag || tag == genTag || tag == asyncTag || tag == proxyTag;
}
var coreJsData = root["__core-js_shared__"];
var maskSrcKey = function() {
  var uid = /[^.]+$/.exec(coreJsData && coreJsData.keys && coreJsData.keys.IE_PROTO || "");
  return uid ? "Symbol(src)_1." + uid : "";
}();
function isMasked(func2) {
  return !!maskSrcKey && maskSrcKey in func2;
}
var funcProto = Function.prototype;
var funcToString = funcProto.toString;
function toSource(func2) {
  if (func2 != null) {
    try {
      return funcToString.call(func2);
    } catch (e) {
    }
    try {
      return func2 + "";
    } catch (e) {
    }
  }
  return "";
}
var reRegExpChar = /[\\^$.*+?()[\]{}|]/g;
var reIsHostCtor = /^\[object .+?Constructor\]$/;
var funcProto$1 = Function.prototype, objectProto$2 = Object.prototype;
var funcToString$1 = funcProto$1.toString;
var hasOwnProperty$1$1 = objectProto$2.hasOwnProperty;
var reIsNative = RegExp("^" + funcToString$1.call(hasOwnProperty$1$1).replace(reRegExpChar, "\\$&").replace(/hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g, "$1.*?") + "$");
function baseIsNative(value) {
  if (!isObject$1(value) || isMasked(value)) {
    return false;
  }
  var pattern = isFunction$1(value) ? reIsNative : reIsHostCtor;
  return pattern.test(toSource(value));
}
function getValue(object2, key) {
  return object2 == null ? void 0 : object2[key];
}
function getNative(object2, key) {
  var value = getValue(object2, key);
  return baseIsNative(value) ? value : void 0;
}
var WeakMap = getNative(root, "WeakMap");
var metaMap = WeakMap && new WeakMap();
var baseSetData = !metaMap ? identity$1 : function(func2, data) {
  metaMap.set(func2, data);
  return func2;
};
var objectCreate = Object.create;
var baseCreate = function() {
  function object2() {
  }
  return function(proto) {
    if (!isObject$1(proto)) {
      return {};
    }
    if (objectCreate) {
      return objectCreate(proto);
    }
    object2.prototype = proto;
    var result2 = new object2();
    object2.prototype = void 0;
    return result2;
  };
}();
function createCtor(Ctor) {
  return function() {
    var args = arguments;
    switch (args.length) {
      case 0:
        return new Ctor();
      case 1:
        return new Ctor(args[0]);
      case 2:
        return new Ctor(args[0], args[1]);
      case 3:
        return new Ctor(args[0], args[1], args[2]);
      case 4:
        return new Ctor(args[0], args[1], args[2], args[3]);
      case 5:
        return new Ctor(args[0], args[1], args[2], args[3], args[4]);
      case 6:
        return new Ctor(args[0], args[1], args[2], args[3], args[4], args[5]);
      case 7:
        return new Ctor(args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
    }
    var thisBinding = baseCreate(Ctor.prototype), result2 = Ctor.apply(thisBinding, args);
    return isObject$1(result2) ? result2 : thisBinding;
  };
}
var WRAP_BIND_FLAG = 1;
function createBind(func2, bitmask, thisArg) {
  var isBind = bitmask & WRAP_BIND_FLAG, Ctor = createCtor(func2);
  function wrapper() {
    var fn = this && this !== root && this instanceof wrapper ? Ctor : func2;
    return fn.apply(isBind ? thisArg : this, arguments);
  }
  return wrapper;
}
function apply(func2, thisArg, args) {
  switch (args.length) {
    case 0:
      return func2.call(thisArg);
    case 1:
      return func2.call(thisArg, args[0]);
    case 2:
      return func2.call(thisArg, args[0], args[1]);
    case 3:
      return func2.call(thisArg, args[0], args[1], args[2]);
  }
  return func2.apply(thisArg, args);
}
var nativeMax = Math.max;
function composeArgs(args, partials, holders, isCurried) {
  var argsIndex = -1, argsLength = args.length, holdersLength = holders.length, leftIndex = -1, leftLength = partials.length, rangeLength = nativeMax(argsLength - holdersLength, 0), result2 = Array(leftLength + rangeLength), isUncurried = !isCurried;
  while (++leftIndex < leftLength) {
    result2[leftIndex] = partials[leftIndex];
  }
  while (++argsIndex < holdersLength) {
    if (isUncurried || argsIndex < argsLength) {
      result2[holders[argsIndex]] = args[argsIndex];
    }
  }
  while (rangeLength--) {
    result2[leftIndex++] = args[argsIndex++];
  }
  return result2;
}
var nativeMax$1 = Math.max;
function composeArgsRight(args, partials, holders, isCurried) {
  var argsIndex = -1, argsLength = args.length, holdersIndex = -1, holdersLength = holders.length, rightIndex = -1, rightLength = partials.length, rangeLength = nativeMax$1(argsLength - holdersLength, 0), result2 = Array(rangeLength + rightLength), isUncurried = !isCurried;
  while (++argsIndex < rangeLength) {
    result2[argsIndex] = args[argsIndex];
  }
  var offset = argsIndex;
  while (++rightIndex < rightLength) {
    result2[offset + rightIndex] = partials[rightIndex];
  }
  while (++holdersIndex < holdersLength) {
    if (isUncurried || argsIndex < argsLength) {
      result2[offset + holders[holdersIndex]] = args[argsIndex++];
    }
  }
  return result2;
}
function countHolders(array2, placeholder) {
  var length = array2.length, result2 = 0;
  while (length--) {
    if (array2[length] === placeholder) {
      ++result2;
    }
  }
  return result2;
}
function baseLodash() {
}
var MAX_ARRAY_LENGTH = 4294967295;
function LazyWrapper(value) {
  this.__wrapped__ = value;
  this.__actions__ = [];
  this.__dir__ = 1;
  this.__filtered__ = false;
  this.__iteratees__ = [];
  this.__takeCount__ = MAX_ARRAY_LENGTH;
  this.__views__ = [];
}
LazyWrapper.prototype = baseCreate(baseLodash.prototype);
LazyWrapper.prototype.constructor = LazyWrapper;
function noop$2() {
}
var getData = !metaMap ? noop$2 : function(func2) {
  return metaMap.get(func2);
};
var realNames = {};
var objectProto$3 = Object.prototype;
var hasOwnProperty$2 = objectProto$3.hasOwnProperty;
function getFuncName(func2) {
  var result2 = func2.name + "", array2 = realNames[result2], length = hasOwnProperty$2.call(realNames, result2) ? array2.length : 0;
  while (length--) {
    var data = array2[length], otherFunc = data.func;
    if (otherFunc == null || otherFunc == func2) {
      return data.name;
    }
  }
  return result2;
}
function LodashWrapper(value, chainAll) {
  this.__wrapped__ = value;
  this.__actions__ = [];
  this.__chain__ = !!chainAll;
  this.__index__ = 0;
  this.__values__ = void 0;
}
LodashWrapper.prototype = baseCreate(baseLodash.prototype);
LodashWrapper.prototype.constructor = LodashWrapper;
function copyArray(source, array2) {
  var index = -1, length = source.length;
  array2 || (array2 = Array(length));
  while (++index < length) {
    array2[index] = source[index];
  }
  return array2;
}
function wrapperClone(wrapper) {
  if (wrapper instanceof LazyWrapper) {
    return wrapper.clone();
  }
  var result2 = new LodashWrapper(wrapper.__wrapped__, wrapper.__chain__);
  result2.__actions__ = copyArray(wrapper.__actions__);
  result2.__index__ = wrapper.__index__;
  result2.__values__ = wrapper.__values__;
  return result2;
}
var objectProto$4 = Object.prototype;
var hasOwnProperty$3 = objectProto$4.hasOwnProperty;
function lodash(value) {
  if (isObjectLike(value) && !isArray$2(value) && !(value instanceof LazyWrapper)) {
    if (value instanceof LodashWrapper) {
      return value;
    }
    if (hasOwnProperty$3.call(value, "__wrapped__")) {
      return wrapperClone(value);
    }
  }
  return new LodashWrapper(value);
}
lodash.prototype = baseLodash.prototype;
lodash.prototype.constructor = lodash;
function isLaziable(func2) {
  var funcName = getFuncName(func2), other = lodash[funcName];
  if (typeof other != "function" || !(funcName in LazyWrapper.prototype)) {
    return false;
  }
  if (func2 === other) {
    return true;
  }
  var data = getData(other);
  return !!data && func2 === data[0];
}
var HOT_COUNT = 800, HOT_SPAN = 16;
var nativeNow = Date.now;
function shortOut(func2) {
  var count = 0, lastCalled = 0;
  return function() {
    var stamp = nativeNow(), remaining = HOT_SPAN - (stamp - lastCalled);
    lastCalled = stamp;
    if (remaining > 0) {
      if (++count >= HOT_COUNT) {
        return arguments[0];
      }
    } else {
      count = 0;
    }
    return func2.apply(void 0, arguments);
  };
}
var setData = shortOut(baseSetData);
var reWrapDetails = /\{\n\/\* \[wrapped with (.+)\] \*/, reSplitDetails = /,? & /;
function getWrapDetails(source) {
  var match = source.match(reWrapDetails);
  return match ? match[1].split(reSplitDetails) : [];
}
var reWrapComment = /\{(?:\n\/\* \[wrapped with .+\] \*\/)?\n?/;
function insertWrapDetails(source, details) {
  var length = details.length;
  if (!length) {
    return source;
  }
  var lastIndex = length - 1;
  details[lastIndex] = (length > 1 ? "& " : "") + details[lastIndex];
  details = details.join(length > 2 ? ", " : " ");
  return source.replace(reWrapComment, "{\n/* [wrapped with " + details + "] */\n");
}
function constant(value) {
  return function() {
    return value;
  };
}
var defineProperty = function() {
  try {
    var func2 = getNative(Object, "defineProperty");
    func2({}, "", {});
    return func2;
  } catch (e) {
  }
}();
var baseSetToString = !defineProperty ? identity$1 : function(func2, string2) {
  return defineProperty(func2, "toString", {
    configurable: true,
    enumerable: false,
    value: constant(string2),
    writable: true
  });
};
var setToString = shortOut(baseSetToString);
function arrayEach(array2, iteratee2) {
  var index = -1, length = array2 == null ? 0 : array2.length;
  while (++index < length) {
    if (iteratee2(array2[index], index, array2) === false) {
      break;
    }
  }
  return array2;
}
function baseFindIndex(array2, predicate, fromIndex, fromRight) {
  var length = array2.length, index = fromIndex + (fromRight ? 1 : -1);
  while (fromRight ? index-- : ++index < length) {
    if (predicate(array2[index], index, array2)) {
      return index;
    }
  }
  return -1;
}
function baseIsNaN(value) {
  return value !== value;
}
function strictIndexOf(array2, value, fromIndex) {
  var index = fromIndex - 1, length = array2.length;
  while (++index < length) {
    if (array2[index] === value) {
      return index;
    }
  }
  return -1;
}
function baseIndexOf(array2, value, fromIndex) {
  return value === value ? strictIndexOf(array2, value, fromIndex) : baseFindIndex(array2, baseIsNaN, fromIndex);
}
function arrayIncludes(array2, value) {
  var length = array2 == null ? 0 : array2.length;
  return !!length && baseIndexOf(array2, value, 0) > -1;
}
var WRAP_BIND_FLAG$1 = 1, WRAP_BIND_KEY_FLAG = 2, WRAP_CURRY_FLAG = 8, WRAP_CURRY_RIGHT_FLAG = 16, WRAP_PARTIAL_FLAG = 32, WRAP_PARTIAL_RIGHT_FLAG = 64, WRAP_ARY_FLAG = 128, WRAP_REARG_FLAG = 256, WRAP_FLIP_FLAG = 512;
var wrapFlags = [
  ["ary", WRAP_ARY_FLAG],
  ["bind", WRAP_BIND_FLAG$1],
  ["bindKey", WRAP_BIND_KEY_FLAG],
  ["curry", WRAP_CURRY_FLAG],
  ["curryRight", WRAP_CURRY_RIGHT_FLAG],
  ["flip", WRAP_FLIP_FLAG],
  ["partial", WRAP_PARTIAL_FLAG],
  ["partialRight", WRAP_PARTIAL_RIGHT_FLAG],
  ["rearg", WRAP_REARG_FLAG]
];
function updateWrapDetails(details, bitmask) {
  arrayEach(wrapFlags, function(pair) {
    var value = "_." + pair[0];
    if (bitmask & pair[1] && !arrayIncludes(details, value)) {
      details.push(value);
    }
  });
  return details.sort();
}
function setWrapToString(wrapper, reference, bitmask) {
  var source = reference + "";
  return setToString(wrapper, insertWrapDetails(source, updateWrapDetails(getWrapDetails(source), bitmask)));
}
var WRAP_BIND_FLAG$2 = 1, WRAP_BIND_KEY_FLAG$1 = 2, WRAP_CURRY_BOUND_FLAG = 4, WRAP_CURRY_FLAG$1 = 8, WRAP_PARTIAL_FLAG$1 = 32, WRAP_PARTIAL_RIGHT_FLAG$1 = 64;
function createRecurry(func2, bitmask, wrapFunc, placeholder, thisArg, partials, holders, argPos, ary2, arity) {
  var isCurry = bitmask & WRAP_CURRY_FLAG$1, newHolders = isCurry ? holders : void 0, newHoldersRight = isCurry ? void 0 : holders, newPartials = isCurry ? partials : void 0, newPartialsRight = isCurry ? void 0 : partials;
  bitmask |= isCurry ? WRAP_PARTIAL_FLAG$1 : WRAP_PARTIAL_RIGHT_FLAG$1;
  bitmask &= ~(isCurry ? WRAP_PARTIAL_RIGHT_FLAG$1 : WRAP_PARTIAL_FLAG$1);
  if (!(bitmask & WRAP_CURRY_BOUND_FLAG)) {
    bitmask &= ~(WRAP_BIND_FLAG$2 | WRAP_BIND_KEY_FLAG$1);
  }
  var newData = [
    func2,
    bitmask,
    thisArg,
    newPartials,
    newHolders,
    newPartialsRight,
    newHoldersRight,
    argPos,
    ary2,
    arity
  ];
  var result2 = wrapFunc.apply(void 0, newData);
  if (isLaziable(func2)) {
    setData(result2, newData);
  }
  result2.placeholder = placeholder;
  return setWrapToString(result2, func2, bitmask);
}
function getHolder(func2) {
  var object2 = func2;
  return object2.placeholder;
}
var MAX_SAFE_INTEGER = 9007199254740991;
var reIsUint = /^(?:0|[1-9]\d*)$/;
function isIndex(value, length) {
  var type = typeof value;
  length = length == null ? MAX_SAFE_INTEGER : length;
  return !!length && (type == "number" || type != "symbol" && reIsUint.test(value)) && (value > -1 && value % 1 == 0 && value < length);
}
var nativeMin = Math.min;
function reorder(array2, indexes) {
  var arrLength = array2.length, length = nativeMin(indexes.length, arrLength), oldArray = copyArray(array2);
  while (length--) {
    var index = indexes[length];
    array2[length] = isIndex(index, arrLength) ? oldArray[index] : void 0;
  }
  return array2;
}
var PLACEHOLDER = "__lodash_placeholder__";
function replaceHolders(array2, placeholder) {
  var index = -1, length = array2.length, resIndex = 0, result2 = [];
  while (++index < length) {
    var value = array2[index];
    if (value === placeholder || value === PLACEHOLDER) {
      array2[index] = PLACEHOLDER;
      result2[resIndex++] = index;
    }
  }
  return result2;
}
var WRAP_BIND_FLAG$3 = 1, WRAP_BIND_KEY_FLAG$2 = 2, WRAP_CURRY_FLAG$2 = 8, WRAP_CURRY_RIGHT_FLAG$1 = 16, WRAP_ARY_FLAG$1 = 128, WRAP_FLIP_FLAG$1 = 512;
function createHybrid(func2, bitmask, thisArg, partials, holders, partialsRight, holdersRight, argPos, ary2, arity) {
  var isAry = bitmask & WRAP_ARY_FLAG$1, isBind = bitmask & WRAP_BIND_FLAG$3, isBindKey = bitmask & WRAP_BIND_KEY_FLAG$2, isCurried = bitmask & (WRAP_CURRY_FLAG$2 | WRAP_CURRY_RIGHT_FLAG$1), isFlip = bitmask & WRAP_FLIP_FLAG$1, Ctor = isBindKey ? void 0 : createCtor(func2);
  function wrapper() {
    var length = arguments.length, args = Array(length), index = length;
    while (index--) {
      args[index] = arguments[index];
    }
    if (isCurried) {
      var placeholder = getHolder(wrapper), holdersCount = countHolders(args, placeholder);
    }
    if (partials) {
      args = composeArgs(args, partials, holders, isCurried);
    }
    if (partialsRight) {
      args = composeArgsRight(args, partialsRight, holdersRight, isCurried);
    }
    length -= holdersCount;
    if (isCurried && length < arity) {
      var newHolders = replaceHolders(args, placeholder);
      return createRecurry(func2, bitmask, createHybrid, wrapper.placeholder, thisArg, args, newHolders, argPos, ary2, arity - length);
    }
    var thisBinding = isBind ? thisArg : this, fn = isBindKey ? thisBinding[func2] : func2;
    length = args.length;
    if (argPos) {
      args = reorder(args, argPos);
    } else if (isFlip && length > 1) {
      args.reverse();
    }
    if (isAry && ary2 < length) {
      args.length = ary2;
    }
    if (this && this !== root && this instanceof wrapper) {
      fn = Ctor || createCtor(fn);
    }
    return fn.apply(thisBinding, args);
  }
  return wrapper;
}
function createCurry(func2, bitmask, arity) {
  var Ctor = createCtor(func2);
  function wrapper() {
    var length = arguments.length, args = Array(length), index = length, placeholder = getHolder(wrapper);
    while (index--) {
      args[index] = arguments[index];
    }
    var holders = length < 3 && args[0] !== placeholder && args[length - 1] !== placeholder ? [] : replaceHolders(args, placeholder);
    length -= holders.length;
    if (length < arity) {
      return createRecurry(func2, bitmask, createHybrid, wrapper.placeholder, void 0, args, holders, void 0, void 0, arity - length);
    }
    var fn = this && this !== root && this instanceof wrapper ? Ctor : func2;
    return apply(fn, this, args);
  }
  return wrapper;
}
var WRAP_BIND_FLAG$4 = 1;
function createPartial(func2, bitmask, thisArg, partials) {
  var isBind = bitmask & WRAP_BIND_FLAG$4, Ctor = createCtor(func2);
  function wrapper() {
    var argsIndex = -1, argsLength = arguments.length, leftIndex = -1, leftLength = partials.length, args = Array(leftLength + argsLength), fn = this && this !== root && this instanceof wrapper ? Ctor : func2;
    while (++leftIndex < leftLength) {
      args[leftIndex] = partials[leftIndex];
    }
    while (argsLength--) {
      args[leftIndex++] = arguments[++argsIndex];
    }
    return apply(fn, isBind ? thisArg : this, args);
  }
  return wrapper;
}
var PLACEHOLDER$1 = "__lodash_placeholder__";
var WRAP_BIND_FLAG$5 = 1, WRAP_BIND_KEY_FLAG$3 = 2, WRAP_CURRY_BOUND_FLAG$1 = 4, WRAP_CURRY_FLAG$3 = 8, WRAP_ARY_FLAG$2 = 128, WRAP_REARG_FLAG$1 = 256;
var nativeMin$1 = Math.min;
function mergeData(data, source) {
  var bitmask = data[1], srcBitmask = source[1], newBitmask = bitmask | srcBitmask, isCommon = newBitmask < (WRAP_BIND_FLAG$5 | WRAP_BIND_KEY_FLAG$3 | WRAP_ARY_FLAG$2);
  var isCombo = srcBitmask == WRAP_ARY_FLAG$2 && bitmask == WRAP_CURRY_FLAG$3 || srcBitmask == WRAP_ARY_FLAG$2 && bitmask == WRAP_REARG_FLAG$1 && data[7].length <= source[8] || srcBitmask == (WRAP_ARY_FLAG$2 | WRAP_REARG_FLAG$1) && source[7].length <= source[8] && bitmask == WRAP_CURRY_FLAG$3;
  if (!(isCommon || isCombo)) {
    return data;
  }
  if (srcBitmask & WRAP_BIND_FLAG$5) {
    data[2] = source[2];
    newBitmask |= bitmask & WRAP_BIND_FLAG$5 ? 0 : WRAP_CURRY_BOUND_FLAG$1;
  }
  var value = source[3];
  if (value) {
    var partials = data[3];
    data[3] = partials ? composeArgs(partials, value, source[4]) : value;
    data[4] = partials ? replaceHolders(data[3], PLACEHOLDER$1) : source[4];
  }
  value = source[5];
  if (value) {
    partials = data[5];
    data[5] = partials ? composeArgsRight(partials, value, source[6]) : value;
    data[6] = partials ? replaceHolders(data[5], PLACEHOLDER$1) : source[6];
  }
  value = source[7];
  if (value) {
    data[7] = value;
  }
  if (srcBitmask & WRAP_ARY_FLAG$2) {
    data[8] = data[8] == null ? source[8] : nativeMin$1(data[8], source[8]);
  }
  if (data[9] == null) {
    data[9] = source[9];
  }
  data[0] = source[0];
  data[1] = newBitmask;
  return data;
}
var FUNC_ERROR_TEXT$1 = "Expected a function";
var WRAP_BIND_FLAG$6 = 1, WRAP_BIND_KEY_FLAG$4 = 2, WRAP_CURRY_FLAG$4 = 8, WRAP_CURRY_RIGHT_FLAG$2 = 16, WRAP_PARTIAL_FLAG$2 = 32, WRAP_PARTIAL_RIGHT_FLAG$2 = 64;
var nativeMax$2 = Math.max;
function createWrap(func2, bitmask, thisArg, partials, holders, argPos, ary2, arity) {
  var isBindKey = bitmask & WRAP_BIND_KEY_FLAG$4;
  if (!isBindKey && typeof func2 != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$1);
  }
  var length = partials ? partials.length : 0;
  if (!length) {
    bitmask &= ~(WRAP_PARTIAL_FLAG$2 | WRAP_PARTIAL_RIGHT_FLAG$2);
    partials = holders = void 0;
  }
  ary2 = ary2 === void 0 ? ary2 : nativeMax$2(toInteger(ary2), 0);
  arity = arity === void 0 ? arity : toInteger(arity);
  length -= holders ? holders.length : 0;
  if (bitmask & WRAP_PARTIAL_RIGHT_FLAG$2) {
    var partialsRight = partials, holdersRight = holders;
    partials = holders = void 0;
  }
  var data = isBindKey ? void 0 : getData(func2);
  var newData = [
    func2,
    bitmask,
    thisArg,
    partials,
    holders,
    partialsRight,
    holdersRight,
    argPos,
    ary2,
    arity
  ];
  if (data) {
    mergeData(newData, data);
  }
  func2 = newData[0];
  bitmask = newData[1];
  thisArg = newData[2];
  partials = newData[3];
  holders = newData[4];
  arity = newData[9] = newData[9] === void 0 ? isBindKey ? 0 : func2.length : nativeMax$2(newData[9] - length, 0);
  if (!arity && bitmask & (WRAP_CURRY_FLAG$4 | WRAP_CURRY_RIGHT_FLAG$2)) {
    bitmask &= ~(WRAP_CURRY_FLAG$4 | WRAP_CURRY_RIGHT_FLAG$2);
  }
  if (!bitmask || bitmask == WRAP_BIND_FLAG$6) {
    var result2 = createBind(func2, bitmask, thisArg);
  } else if (bitmask == WRAP_CURRY_FLAG$4 || bitmask == WRAP_CURRY_RIGHT_FLAG$2) {
    result2 = createCurry(func2, bitmask, arity);
  } else if ((bitmask == WRAP_PARTIAL_FLAG$2 || bitmask == (WRAP_BIND_FLAG$6 | WRAP_PARTIAL_FLAG$2)) && !holders.length) {
    result2 = createPartial(func2, bitmask, thisArg, partials);
  } else {
    result2 = createHybrid.apply(void 0, newData);
  }
  var setter = data ? baseSetData : setData;
  return setWrapToString(setter(result2, newData), func2, bitmask);
}
var WRAP_ARY_FLAG$3 = 128;
function ary(func2, n, guard) {
  n = guard ? void 0 : n;
  n = func2 && n == null ? func2.length : n;
  return createWrap(func2, WRAP_ARY_FLAG$3, void 0, void 0, void 0, void 0, n);
}
function baseAssignValue(object2, key, value) {
  if (key == "__proto__" && defineProperty) {
    defineProperty(object2, key, {
      configurable: true,
      enumerable: true,
      value,
      writable: true
    });
  } else {
    object2[key] = value;
  }
}
function eq(value, other) {
  return value === other || value !== value && other !== other;
}
var objectProto$5 = Object.prototype;
var hasOwnProperty$4 = objectProto$5.hasOwnProperty;
function assignValue(object2, key, value) {
  var objValue = object2[key];
  if (!(hasOwnProperty$4.call(object2, key) && eq(objValue, value)) || value === void 0 && !(key in object2)) {
    baseAssignValue(object2, key, value);
  }
}
function copyObject(source, props, object2, customizer) {
  var isNew = !object2;
  object2 || (object2 = {});
  var index = -1, length = props.length;
  while (++index < length) {
    var key = props[index];
    var newValue = customizer ? customizer(object2[key], source[key], key, object2, source) : void 0;
    if (newValue === void 0) {
      newValue = source[key];
    }
    if (isNew) {
      baseAssignValue(object2, key, newValue);
    } else {
      assignValue(object2, key, newValue);
    }
  }
  return object2;
}
var nativeMax$3 = Math.max;
function overRest(func2, start, transform2) {
  start = nativeMax$3(start === void 0 ? func2.length - 1 : start, 0);
  return function() {
    var args = arguments, index = -1, length = nativeMax$3(args.length - start, 0), array2 = Array(length);
    while (++index < length) {
      array2[index] = args[start + index];
    }
    index = -1;
    var otherArgs = Array(start + 1);
    while (++index < start) {
      otherArgs[index] = args[index];
    }
    otherArgs[start] = transform2(array2);
    return apply(func2, this, otherArgs);
  };
}
function baseRest(func2, start) {
  return setToString(overRest(func2, start, identity$1), func2 + "");
}
var MAX_SAFE_INTEGER$1 = 9007199254740991;
function isLength(value) {
  return typeof value == "number" && value > -1 && value % 1 == 0 && value <= MAX_SAFE_INTEGER$1;
}
function isArrayLike(value) {
  return value != null && isLength(value.length) && !isFunction$1(value);
}
function isIterateeCall(value, index, object2) {
  if (!isObject$1(object2)) {
    return false;
  }
  var type = typeof index;
  if (type == "number" ? isArrayLike(object2) && isIndex(index, object2.length) : type == "string" && index in object2) {
    return eq(object2[index], value);
  }
  return false;
}
function createAssigner(assigner) {
  return baseRest(function(object2, sources) {
    var index = -1, length = sources.length, customizer = length > 1 ? sources[length - 1] : void 0, guard = length > 2 ? sources[2] : void 0;
    customizer = assigner.length > 3 && typeof customizer == "function" ? (length--, customizer) : void 0;
    if (guard && isIterateeCall(sources[0], sources[1], guard)) {
      customizer = length < 3 ? void 0 : customizer;
      length = 1;
    }
    object2 = Object(object2);
    while (++index < length) {
      var source = sources[index];
      if (source) {
        assigner(object2, source, index, customizer);
      }
    }
    return object2;
  });
}
var objectProto$6 = Object.prototype;
function isPrototype(value) {
  var Ctor = value && value.constructor, proto = typeof Ctor == "function" && Ctor.prototype || objectProto$6;
  return value === proto;
}
function baseTimes(n, iteratee2) {
  var index = -1, result2 = Array(n);
  while (++index < n) {
    result2[index] = iteratee2(index);
  }
  return result2;
}
var argsTag = "[object Arguments]";
function baseIsArguments(value) {
  return isObjectLike(value) && baseGetTag(value) == argsTag;
}
var objectProto$7 = Object.prototype;
var hasOwnProperty$5 = objectProto$7.hasOwnProperty;
var propertyIsEnumerable = objectProto$7.propertyIsEnumerable;
var isArguments = baseIsArguments(function() {
  return arguments;
}()) ? baseIsArguments : function(value) {
  return isObjectLike(value) && hasOwnProperty$5.call(value, "callee") && !propertyIsEnumerable.call(value, "callee");
};
function stubFalse() {
  return false;
}
var freeExports = typeof exports == "object" && exports && !exports.nodeType && exports;
var freeModule = freeExports && typeof module == "object" && module && !module.nodeType && module;
var moduleExports = freeModule && freeModule.exports === freeExports;
var Buffer$1 = moduleExports ? root.Buffer : void 0;
var nativeIsBuffer = Buffer$1 ? Buffer$1.isBuffer : void 0;
var isBuffer$2 = nativeIsBuffer || stubFalse;
var argsTag$1 = "[object Arguments]", arrayTag = "[object Array]", boolTag = "[object Boolean]", dateTag = "[object Date]", errorTag = "[object Error]", funcTag$1 = "[object Function]", mapTag = "[object Map]", numberTag = "[object Number]", objectTag = "[object Object]", regexpTag = "[object RegExp]", setTag = "[object Set]", stringTag = "[object String]", weakMapTag = "[object WeakMap]";
var arrayBufferTag = "[object ArrayBuffer]", dataViewTag = "[object DataView]", float32Tag = "[object Float32Array]", float64Tag = "[object Float64Array]", int8Tag = "[object Int8Array]", int16Tag = "[object Int16Array]", int32Tag = "[object Int32Array]", uint8Tag = "[object Uint8Array]", uint8ClampedTag = "[object Uint8ClampedArray]", uint16Tag = "[object Uint16Array]", uint32Tag = "[object Uint32Array]";
var typedArrayTags = {};
typedArrayTags[float32Tag] = typedArrayTags[float64Tag] = typedArrayTags[int8Tag] = typedArrayTags[int16Tag] = typedArrayTags[int32Tag] = typedArrayTags[uint8Tag] = typedArrayTags[uint8ClampedTag] = typedArrayTags[uint16Tag] = typedArrayTags[uint32Tag] = true;
typedArrayTags[argsTag$1] = typedArrayTags[arrayTag] = typedArrayTags[arrayBufferTag] = typedArrayTags[boolTag] = typedArrayTags[dataViewTag] = typedArrayTags[dateTag] = typedArrayTags[errorTag] = typedArrayTags[funcTag$1] = typedArrayTags[mapTag] = typedArrayTags[numberTag] = typedArrayTags[objectTag] = typedArrayTags[regexpTag] = typedArrayTags[setTag] = typedArrayTags[stringTag] = typedArrayTags[weakMapTag] = false;
function baseIsTypedArray(value) {
  return isObjectLike(value) && isLength(value.length) && !!typedArrayTags[baseGetTag(value)];
}
function baseUnary(func2) {
  return function(value) {
    return func2(value);
  };
}
var freeExports$1 = typeof exports == "object" && exports && !exports.nodeType && exports;
var freeModule$1 = freeExports$1 && typeof module == "object" && module && !module.nodeType && module;
var moduleExports$1 = freeModule$1 && freeModule$1.exports === freeExports$1;
var freeProcess = moduleExports$1 && freeGlobal.process;
var nodeUtil = function() {
  try {
    var types = freeModule$1 && freeModule$1.require && freeModule$1.require("util").types;
    if (types) {
      return types;
    }
    return freeProcess && freeProcess.binding && freeProcess.binding("util");
  } catch (e) {
  }
}();
var nodeIsTypedArray = nodeUtil && nodeUtil.isTypedArray;
var isTypedArray$1 = nodeIsTypedArray ? baseUnary(nodeIsTypedArray) : baseIsTypedArray;
var objectProto$8 = Object.prototype;
var hasOwnProperty$6 = objectProto$8.hasOwnProperty;
function arrayLikeKeys(value, inherited) {
  var isArr = isArray$2(value), isArg = !isArr && isArguments(value), isBuff = !isArr && !isArg && isBuffer$2(value), isType = !isArr && !isArg && !isBuff && isTypedArray$1(value), skipIndexes = isArr || isArg || isBuff || isType, result2 = skipIndexes ? baseTimes(value.length, String) : [], length = result2.length;
  for (var key in value) {
    if ((inherited || hasOwnProperty$6.call(value, key)) && !(skipIndexes && (key == "length" || isBuff && (key == "offset" || key == "parent") || isType && (key == "buffer" || key == "byteLength" || key == "byteOffset") || isIndex(key, length)))) {
      result2.push(key);
    }
  }
  return result2;
}
function overArg(func2, transform2) {
  return function(arg) {
    return func2(transform2(arg));
  };
}
var nativeKeys = overArg(Object.keys, Object);
var objectProto$9 = Object.prototype;
var hasOwnProperty$7 = objectProto$9.hasOwnProperty;
function baseKeys(object2) {
  if (!isPrototype(object2)) {
    return nativeKeys(object2);
  }
  var result2 = [];
  for (var key in Object(object2)) {
    if (hasOwnProperty$7.call(object2, key) && key != "constructor") {
      result2.push(key);
    }
  }
  return result2;
}
function keys(object2) {
  return isArrayLike(object2) ? arrayLikeKeys(object2) : baseKeys(object2);
}
var objectProto$a = Object.prototype;
var hasOwnProperty$8 = objectProto$a.hasOwnProperty;
var assign$1 = createAssigner(function(object2, source) {
  if (isPrototype(source) || isArrayLike(source)) {
    copyObject(source, keys(source), object2);
    return;
  }
  for (var key in source) {
    if (hasOwnProperty$8.call(source, key)) {
      assignValue(object2, key, source[key]);
    }
  }
});
function nativeKeysIn(object2) {
  var result2 = [];
  if (object2 != null) {
    for (var key in Object(object2)) {
      result2.push(key);
    }
  }
  return result2;
}
var objectProto$b = Object.prototype;
var hasOwnProperty$9 = objectProto$b.hasOwnProperty;
function baseKeysIn(object2) {
  if (!isObject$1(object2)) {
    return nativeKeysIn(object2);
  }
  var isProto = isPrototype(object2), result2 = [];
  for (var key in object2) {
    if (!(key == "constructor" && (isProto || !hasOwnProperty$9.call(object2, key)))) {
      result2.push(key);
    }
  }
  return result2;
}
function keysIn(object2) {
  return isArrayLike(object2) ? arrayLikeKeys(object2, true) : baseKeysIn(object2);
}
var assignIn = createAssigner(function(object2, source) {
  copyObject(source, keysIn(source), object2);
});
var assignInWith = createAssigner(function(object2, source, srcIndex, customizer) {
  copyObject(source, keysIn(source), object2, customizer);
});
var assignWith = createAssigner(function(object2, source, srcIndex, customizer) {
  copyObject(source, keys(source), object2, customizer);
});
var reIsDeepProp = /\.|\[(?:[^[\]]*|(["'])(?:(?!\1)[^\\]|\\.)*?\1)\]/, reIsPlainProp = /^\w*$/;
function isKey(value, object2) {
  if (isArray$2(value)) {
    return false;
  }
  var type = typeof value;
  if (type == "number" || type == "symbol" || type == "boolean" || value == null || isSymbol(value)) {
    return true;
  }
  return reIsPlainProp.test(value) || !reIsDeepProp.test(value) || object2 != null && value in Object(object2);
}
var nativeCreate = getNative(Object, "create");
function hashClear() {
  this.__data__ = nativeCreate ? nativeCreate(null) : {};
  this.size = 0;
}
function hashDelete(key) {
  var result2 = this.has(key) && delete this.__data__[key];
  this.size -= result2 ? 1 : 0;
  return result2;
}
var HASH_UNDEFINED = "__lodash_hash_undefined__";
var objectProto$c = Object.prototype;
var hasOwnProperty$a = objectProto$c.hasOwnProperty;
function hashGet(key) {
  var data = this.__data__;
  if (nativeCreate) {
    var result2 = data[key];
    return result2 === HASH_UNDEFINED ? void 0 : result2;
  }
  return hasOwnProperty$a.call(data, key) ? data[key] : void 0;
}
var objectProto$d = Object.prototype;
var hasOwnProperty$b = objectProto$d.hasOwnProperty;
function hashHas(key) {
  var data = this.__data__;
  return nativeCreate ? data[key] !== void 0 : hasOwnProperty$b.call(data, key);
}
var HASH_UNDEFINED$1 = "__lodash_hash_undefined__";
function hashSet(key, value) {
  var data = this.__data__;
  this.size += this.has(key) ? 0 : 1;
  data[key] = nativeCreate && value === void 0 ? HASH_UNDEFINED$1 : value;
  return this;
}
function Hash(entries) {
  var index = -1, length = entries == null ? 0 : entries.length;
  this.clear();
  while (++index < length) {
    var entry = entries[index];
    this.set(entry[0], entry[1]);
  }
}
Hash.prototype.clear = hashClear;
Hash.prototype["delete"] = hashDelete;
Hash.prototype.get = hashGet;
Hash.prototype.has = hashHas;
Hash.prototype.set = hashSet;
function listCacheClear() {
  this.__data__ = [];
  this.size = 0;
}
function assocIndexOf(array2, key) {
  var length = array2.length;
  while (length--) {
    if (eq(array2[length][0], key)) {
      return length;
    }
  }
  return -1;
}
var arrayProto = Array.prototype;
var splice = arrayProto.splice;
function listCacheDelete(key) {
  var data = this.__data__, index = assocIndexOf(data, key);
  if (index < 0) {
    return false;
  }
  var lastIndex = data.length - 1;
  if (index == lastIndex) {
    data.pop();
  } else {
    splice.call(data, index, 1);
  }
  --this.size;
  return true;
}
function listCacheGet(key) {
  var data = this.__data__, index = assocIndexOf(data, key);
  return index < 0 ? void 0 : data[index][1];
}
function listCacheHas(key) {
  return assocIndexOf(this.__data__, key) > -1;
}
function listCacheSet(key, value) {
  var data = this.__data__, index = assocIndexOf(data, key);
  if (index < 0) {
    ++this.size;
    data.push([key, value]);
  } else {
    data[index][1] = value;
  }
  return this;
}
function ListCache(entries) {
  var index = -1, length = entries == null ? 0 : entries.length;
  this.clear();
  while (++index < length) {
    var entry = entries[index];
    this.set(entry[0], entry[1]);
  }
}
ListCache.prototype.clear = listCacheClear;
ListCache.prototype["delete"] = listCacheDelete;
ListCache.prototype.get = listCacheGet;
ListCache.prototype.has = listCacheHas;
ListCache.prototype.set = listCacheSet;
var Map$1 = getNative(root, "Map");
function mapCacheClear() {
  this.size = 0;
  this.__data__ = {
    hash: new Hash(),
    map: new (Map$1 || ListCache)(),
    string: new Hash()
  };
}
function isKeyable(value) {
  var type = typeof value;
  return type == "string" || type == "number" || type == "symbol" || type == "boolean" ? value !== "__proto__" : value === null;
}
function getMapData(map2, key) {
  var data = map2.__data__;
  return isKeyable(key) ? data[typeof key == "string" ? "string" : "hash"] : data.map;
}
function mapCacheDelete(key) {
  var result2 = getMapData(this, key)["delete"](key);
  this.size -= result2 ? 1 : 0;
  return result2;
}
function mapCacheGet(key) {
  return getMapData(this, key).get(key);
}
function mapCacheHas(key) {
  return getMapData(this, key).has(key);
}
function mapCacheSet(key, value) {
  var data = getMapData(this, key), size2 = data.size;
  data.set(key, value);
  this.size += data.size == size2 ? 0 : 1;
  return this;
}
function MapCache(entries) {
  var index = -1, length = entries == null ? 0 : entries.length;
  this.clear();
  while (++index < length) {
    var entry = entries[index];
    this.set(entry[0], entry[1]);
  }
}
MapCache.prototype.clear = mapCacheClear;
MapCache.prototype["delete"] = mapCacheDelete;
MapCache.prototype.get = mapCacheGet;
MapCache.prototype.has = mapCacheHas;
MapCache.prototype.set = mapCacheSet;
var FUNC_ERROR_TEXT$2 = "Expected a function";
function memoize(func2, resolver) {
  if (typeof func2 != "function" || resolver != null && typeof resolver != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$2);
  }
  var memoized = function() {
    var args = arguments, key = resolver ? resolver.apply(this, args) : args[0], cache = memoized.cache;
    if (cache.has(key)) {
      return cache.get(key);
    }
    var result2 = func2.apply(this, args);
    memoized.cache = cache.set(key, result2) || cache;
    return result2;
  };
  memoized.cache = new (memoize.Cache || MapCache)();
  return memoized;
}
memoize.Cache = MapCache;
var MAX_MEMOIZE_SIZE = 500;
function memoizeCapped(func2) {
  var result2 = memoize(func2, function(key) {
    if (cache.size === MAX_MEMOIZE_SIZE) {
      cache.clear();
    }
    return key;
  });
  var cache = result2.cache;
  return result2;
}
var rePropName = /[^.[\]]+|\[(?:(-?\d+(?:\.\d+)?)|(["'])((?:(?!\2)[^\\]|\\.)*?)\2)\]|(?=(?:\.|\[\])(?:\.|\[\]|$))/g;
var reEscapeChar = /\\(\\)?/g;
var stringToPath = memoizeCapped(function(string2) {
  var result2 = [];
  if (string2.charCodeAt(0) === 46) {
    result2.push("");
  }
  string2.replace(rePropName, function(match, number2, quote, subString) {
    result2.push(quote ? subString.replace(reEscapeChar, "$1") : number2 || match);
  });
  return result2;
});
function toString$2(value) {
  return value == null ? "" : baseToString(value);
}
function castPath(value, object2) {
  if (isArray$2(value)) {
    return value;
  }
  return isKey(value, object2) ? [value] : stringToPath(toString$2(value));
}
var INFINITY$2 = 1 / 0;
function toKey(value) {
  if (typeof value == "string" || isSymbol(value)) {
    return value;
  }
  var result2 = value + "";
  return result2 == "0" && 1 / value == -INFINITY$2 ? "-0" : result2;
}
function baseGet(object2, path) {
  path = castPath(path, object2);
  var index = 0, length = path.length;
  while (object2 != null && index < length) {
    object2 = object2[toKey(path[index++])];
  }
  return index && index == length ? object2 : void 0;
}
function get(object2, path, defaultValue) {
  var result2 = object2 == null ? void 0 : baseGet(object2, path);
  return result2 === void 0 ? defaultValue : result2;
}
function baseAt(object2, paths) {
  var index = -1, length = paths.length, result2 = Array(length), skip = object2 == null;
  while (++index < length) {
    result2[index] = skip ? void 0 : get(object2, paths[index]);
  }
  return result2;
}
function arrayPush(array2, values2) {
  var index = -1, length = values2.length, offset = array2.length;
  while (++index < length) {
    array2[offset + index] = values2[index];
  }
  return array2;
}
var spreadableSymbol = Symbol$1 ? Symbol$1.isConcatSpreadable : void 0;
function isFlattenable(value) {
  return isArray$2(value) || isArguments(value) || !!(spreadableSymbol && value && value[spreadableSymbol]);
}
function baseFlatten(array2, depth, predicate, isStrict, result2) {
  var index = -1, length = array2.length;
  predicate || (predicate = isFlattenable);
  result2 || (result2 = []);
  while (++index < length) {
    var value = array2[index];
    if (depth > 0 && predicate(value)) {
      if (depth > 1) {
        baseFlatten(value, depth - 1, predicate, isStrict, result2);
      } else {
        arrayPush(result2, value);
      }
    } else if (!isStrict) {
      result2[result2.length] = value;
    }
  }
  return result2;
}
function flatten(array2) {
  var length = array2 == null ? 0 : array2.length;
  return length ? baseFlatten(array2, 1) : [];
}
function flatRest(func2) {
  return setToString(overRest(func2, void 0, flatten), func2 + "");
}
var at = flatRest(baseAt);
var getPrototype = overArg(Object.getPrototypeOf, Object);
var objectTag$1 = "[object Object]";
var funcProto$2 = Function.prototype, objectProto$e = Object.prototype;
var funcToString$2 = funcProto$2.toString;
var hasOwnProperty$c = objectProto$e.hasOwnProperty;
var objectCtorString = funcToString$2.call(Object);
function isPlainObject$1(value) {
  if (!isObjectLike(value) || baseGetTag(value) != objectTag$1) {
    return false;
  }
  var proto = getPrototype(value);
  if (proto === null) {
    return true;
  }
  var Ctor = hasOwnProperty$c.call(proto, "constructor") && proto.constructor;
  return typeof Ctor == "function" && Ctor instanceof Ctor && funcToString$2.call(Ctor) == objectCtorString;
}
var domExcTag = "[object DOMException]", errorTag$1 = "[object Error]";
function isError(value) {
  if (!isObjectLike(value)) {
    return false;
  }
  var tag = baseGetTag(value);
  return tag == errorTag$1 || tag == domExcTag || typeof value.message == "string" && typeof value.name == "string" && !isPlainObject$1(value);
}
var attempt = baseRest(function(func2, args) {
  try {
    return apply(func2, void 0, args);
  } catch (e) {
    return isError(e) ? e : new Error(e);
  }
});
var FUNC_ERROR_TEXT$3 = "Expected a function";
function before(n, func2) {
  var result2;
  if (typeof func2 != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$3);
  }
  n = toInteger(n);
  return function() {
    if (--n > 0) {
      result2 = func2.apply(this, arguments);
    }
    if (n <= 1) {
      func2 = void 0;
    }
    return result2;
  };
}
var WRAP_BIND_FLAG$7 = 1, WRAP_PARTIAL_FLAG$3 = 32;
var bind$1 = baseRest(function(func2, thisArg, partials) {
  var bitmask = WRAP_BIND_FLAG$7;
  if (partials.length) {
    var holders = replaceHolders(partials, getHolder(bind$1));
    bitmask |= WRAP_PARTIAL_FLAG$3;
  }
  return createWrap(func2, bitmask, thisArg, partials, holders);
});
bind$1.placeholder = {};
var bindAll = flatRest(function(object2, methodNames) {
  arrayEach(methodNames, function(key) {
    key = toKey(key);
    baseAssignValue(object2, key, bind$1(object2[key], object2));
  });
  return object2;
});
var WRAP_BIND_FLAG$8 = 1, WRAP_BIND_KEY_FLAG$5 = 2, WRAP_PARTIAL_FLAG$4 = 32;
var bindKey = baseRest(function(object2, key, partials) {
  var bitmask = WRAP_BIND_FLAG$8 | WRAP_BIND_KEY_FLAG$5;
  if (partials.length) {
    var holders = replaceHolders(partials, getHolder(bindKey));
    bitmask |= WRAP_PARTIAL_FLAG$4;
  }
  return createWrap(key, bitmask, object2, partials, holders);
});
bindKey.placeholder = {};
function baseSlice(array2, start, end) {
  var index = -1, length = array2.length;
  if (start < 0) {
    start = -start > length ? 0 : length + start;
  }
  end = end > length ? length : end;
  if (end < 0) {
    end += length;
  }
  length = start > end ? 0 : end - start >>> 0;
  start >>>= 0;
  var result2 = Array(length);
  while (++index < length) {
    result2[index] = array2[index + start];
  }
  return result2;
}
function castSlice(array2, start, end) {
  var length = array2.length;
  end = end === void 0 ? length : end;
  return !start && end >= length ? array2 : baseSlice(array2, start, end);
}
var rsAstralRange = "\\ud800-\\udfff", rsComboMarksRange = "\\u0300-\\u036f", reComboHalfMarksRange = "\\ufe20-\\ufe2f", rsComboSymbolsRange = "\\u20d0-\\u20ff", rsComboRange = rsComboMarksRange + reComboHalfMarksRange + rsComboSymbolsRange, rsVarRange = "\\ufe0e\\ufe0f";
var rsZWJ = "\\u200d";
var reHasUnicode = RegExp("[" + rsZWJ + rsAstralRange + rsComboRange + rsVarRange + "]");
function hasUnicode(string2) {
  return reHasUnicode.test(string2);
}
function asciiToArray(string2) {
  return string2.split("");
}
var rsAstralRange$1 = "\\ud800-\\udfff", rsComboMarksRange$1 = "\\u0300-\\u036f", reComboHalfMarksRange$1 = "\\ufe20-\\ufe2f", rsComboSymbolsRange$1 = "\\u20d0-\\u20ff", rsComboRange$1 = rsComboMarksRange$1 + reComboHalfMarksRange$1 + rsComboSymbolsRange$1, rsVarRange$1 = "\\ufe0e\\ufe0f";
var rsAstral = "[" + rsAstralRange$1 + "]", rsCombo = "[" + rsComboRange$1 + "]", rsFitz = "\\ud83c[\\udffb-\\udfff]", rsModifier = "(?:" + rsCombo + "|" + rsFitz + ")", rsNonAstral = "[^" + rsAstralRange$1 + "]", rsRegional = "(?:\\ud83c[\\udde6-\\uddff]){2}", rsSurrPair = "[\\ud800-\\udbff][\\udc00-\\udfff]", rsZWJ$1 = "\\u200d";
var reOptMod = rsModifier + "?", rsOptVar = "[" + rsVarRange$1 + "]?", rsOptJoin = "(?:" + rsZWJ$1 + "(?:" + [rsNonAstral, rsRegional, rsSurrPair].join("|") + ")" + rsOptVar + reOptMod + ")*", rsSeq = rsOptVar + reOptMod + rsOptJoin, rsSymbol = "(?:" + [rsNonAstral + rsCombo + "?", rsCombo, rsRegional, rsSurrPair, rsAstral].join("|") + ")";
var reUnicode = RegExp(rsFitz + "(?=" + rsFitz + ")|" + rsSymbol + rsSeq, "g");
function unicodeToArray(string2) {
  return string2.match(reUnicode) || [];
}
function stringToArray(string2) {
  return hasUnicode(string2) ? unicodeToArray(string2) : asciiToArray(string2);
}
function createCaseFirst(methodName) {
  return function(string2) {
    string2 = toString$2(string2);
    var strSymbols = hasUnicode(string2) ? stringToArray(string2) : void 0;
    var chr = strSymbols ? strSymbols[0] : string2.charAt(0);
    var trailing = strSymbols ? castSlice(strSymbols, 1).join("") : string2.slice(1);
    return chr[methodName]() + trailing;
  };
}
var upperFirst = createCaseFirst("toUpperCase");
function capitalize(string2) {
  return upperFirst(toString$2(string2).toLowerCase());
}
function arrayReduce(array2, iteratee2, accumulator, initAccum) {
  var index = -1, length = array2 == null ? 0 : array2.length;
  if (initAccum && length) {
    accumulator = array2[++index];
  }
  while (++index < length) {
    accumulator = iteratee2(accumulator, array2[index], index, array2);
  }
  return accumulator;
}
function basePropertyOf(object2) {
  return function(key) {
    return object2 == null ? void 0 : object2[key];
  };
}
var deburredLetters = {
  \u00C0: "A",
  \u00C1: "A",
  \u00C2: "A",
  \u00C3: "A",
  \u00C4: "A",
  \u00C5: "A",
  \u00E0: "a",
  \u00E1: "a",
  \u00E2: "a",
  \u00E3: "a",
  \u00E4: "a",
  \u00E5: "a",
  \u00C7: "C",
  \u00E7: "c",
  \u00D0: "D",
  \u00F0: "d",
  \u00C8: "E",
  \u00C9: "E",
  \u00CA: "E",
  \u00CB: "E",
  \u00E8: "e",
  \u00E9: "e",
  \u00EA: "e",
  \u00EB: "e",
  \u00CC: "I",
  \u00CD: "I",
  \u00CE: "I",
  \u00CF: "I",
  \u00EC: "i",
  \u00ED: "i",
  \u00EE: "i",
  \u00EF: "i",
  \u00D1: "N",
  \u00F1: "n",
  \u00D2: "O",
  \u00D3: "O",
  \u00D4: "O",
  \u00D5: "O",
  \u00D6: "O",
  \u00D8: "O",
  \u00F2: "o",
  \u00F3: "o",
  \u00F4: "o",
  \u00F5: "o",
  \u00F6: "o",
  \u00F8: "o",
  \u00D9: "U",
  \u00DA: "U",
  \u00DB: "U",
  \u00DC: "U",
  \u00F9: "u",
  \u00FA: "u",
  \u00FB: "u",
  \u00FC: "u",
  \u00DD: "Y",
  \u00FD: "y",
  \u00FF: "y",
  \u00C6: "Ae",
  \u00E6: "ae",
  \u00DE: "Th",
  \u00FE: "th",
  \u00DF: "ss",
  \u0100: "A",
  \u0102: "A",
  \u0104: "A",
  \u0101: "a",
  \u0103: "a",
  \u0105: "a",
  \u0106: "C",
  \u0108: "C",
  \u010A: "C",
  \u010C: "C",
  \u0107: "c",
  \u0109: "c",
  \u010B: "c",
  \u010D: "c",
  \u010E: "D",
  \u0110: "D",
  \u010F: "d",
  \u0111: "d",
  \u0112: "E",
  \u0114: "E",
  \u0116: "E",
  \u0118: "E",
  \u011A: "E",
  \u0113: "e",
  \u0115: "e",
  \u0117: "e",
  \u0119: "e",
  \u011B: "e",
  \u011C: "G",
  \u011E: "G",
  \u0120: "G",
  \u0122: "G",
  \u011D: "g",
  \u011F: "g",
  \u0121: "g",
  \u0123: "g",
  \u0124: "H",
  \u0126: "H",
  \u0125: "h",
  \u0127: "h",
  \u0128: "I",
  \u012A: "I",
  \u012C: "I",
  \u012E: "I",
  \u0130: "I",
  \u0129: "i",
  \u012B: "i",
  \u012D: "i",
  \u012F: "i",
  \u0131: "i",
  \u0134: "J",
  \u0135: "j",
  \u0136: "K",
  \u0137: "k",
  \u0138: "k",
  \u0139: "L",
  \u013B: "L",
  \u013D: "L",
  \u013F: "L",
  \u0141: "L",
  \u013A: "l",
  \u013C: "l",
  \u013E: "l",
  \u0140: "l",
  \u0142: "l",
  \u0143: "N",
  \u0145: "N",
  \u0147: "N",
  \u014A: "N",
  \u0144: "n",
  \u0146: "n",
  \u0148: "n",
  \u014B: "n",
  \u014C: "O",
  \u014E: "O",
  \u0150: "O",
  \u014D: "o",
  \u014F: "o",
  \u0151: "o",
  \u0154: "R",
  \u0156: "R",
  \u0158: "R",
  \u0155: "r",
  \u0157: "r",
  \u0159: "r",
  \u015A: "S",
  \u015C: "S",
  \u015E: "S",
  \u0160: "S",
  \u015B: "s",
  \u015D: "s",
  \u015F: "s",
  \u0161: "s",
  \u0162: "T",
  \u0164: "T",
  \u0166: "T",
  \u0163: "t",
  \u0165: "t",
  \u0167: "t",
  \u0168: "U",
  \u016A: "U",
  \u016C: "U",
  \u016E: "U",
  \u0170: "U",
  \u0172: "U",
  \u0169: "u",
  \u016B: "u",
  \u016D: "u",
  \u016F: "u",
  \u0171: "u",
  \u0173: "u",
  \u0174: "W",
  \u0175: "w",
  \u0176: "Y",
  \u0177: "y",
  \u0178: "Y",
  \u0179: "Z",
  \u017B: "Z",
  \u017D: "Z",
  \u017A: "z",
  \u017C: "z",
  \u017E: "z",
  \u0132: "IJ",
  \u0133: "ij",
  \u0152: "Oe",
  \u0153: "oe",
  \u0149: "'n",
  \u017F: "s"
};
var deburrLetter = basePropertyOf(deburredLetters);
var reLatin = /[\xc0-\xd6\xd8-\xf6\xf8-\xff\u0100-\u017f]/g;
var rsComboMarksRange$2 = "\\u0300-\\u036f", reComboHalfMarksRange$2 = "\\ufe20-\\ufe2f", rsComboSymbolsRange$2 = "\\u20d0-\\u20ff", rsComboRange$2 = rsComboMarksRange$2 + reComboHalfMarksRange$2 + rsComboSymbolsRange$2;
var rsCombo$1 = "[" + rsComboRange$2 + "]";
var reComboMark = RegExp(rsCombo$1, "g");
function deburr(string2) {
  string2 = toString$2(string2);
  return string2 && string2.replace(reLatin, deburrLetter).replace(reComboMark, "");
}
var reAsciiWord = /[^\x00-\x2f\x3a-\x40\x5b-\x60\x7b-\x7f]+/g;
function asciiWords(string2) {
  return string2.match(reAsciiWord) || [];
}
var reHasUnicodeWord = /[a-z][A-Z]|[A-Z]{2}[a-z]|[0-9][a-zA-Z]|[a-zA-Z][0-9]|[^a-zA-Z0-9 ]/;
function hasUnicodeWord(string2) {
  return reHasUnicodeWord.test(string2);
}
var rsAstralRange$2 = "\\ud800-\\udfff", rsComboMarksRange$3 = "\\u0300-\\u036f", reComboHalfMarksRange$3 = "\\ufe20-\\ufe2f", rsComboSymbolsRange$3 = "\\u20d0-\\u20ff", rsComboRange$3 = rsComboMarksRange$3 + reComboHalfMarksRange$3 + rsComboSymbolsRange$3, rsDingbatRange = "\\u2700-\\u27bf", rsLowerRange = "a-z\\xdf-\\xf6\\xf8-\\xff", rsMathOpRange = "\\xac\\xb1\\xd7\\xf7", rsNonCharRange = "\\x00-\\x2f\\x3a-\\x40\\x5b-\\x60\\x7b-\\xbf", rsPunctuationRange = "\\u2000-\\u206f", rsSpaceRange = " \\t\\x0b\\f\\xa0\\ufeff\\n\\r\\u2028\\u2029\\u1680\\u180e\\u2000\\u2001\\u2002\\u2003\\u2004\\u2005\\u2006\\u2007\\u2008\\u2009\\u200a\\u202f\\u205f\\u3000", rsUpperRange = "A-Z\\xc0-\\xd6\\xd8-\\xde", rsVarRange$2 = "\\ufe0e\\ufe0f", rsBreakRange = rsMathOpRange + rsNonCharRange + rsPunctuationRange + rsSpaceRange;
var rsApos = "['\u2019]", rsBreak = "[" + rsBreakRange + "]", rsCombo$2 = "[" + rsComboRange$3 + "]", rsDigits = "\\d+", rsDingbat = "[" + rsDingbatRange + "]", rsLower = "[" + rsLowerRange + "]", rsMisc = "[^" + rsAstralRange$2 + rsBreakRange + rsDigits + rsDingbatRange + rsLowerRange + rsUpperRange + "]", rsFitz$1 = "\\ud83c[\\udffb-\\udfff]", rsModifier$1 = "(?:" + rsCombo$2 + "|" + rsFitz$1 + ")", rsNonAstral$1 = "[^" + rsAstralRange$2 + "]", rsRegional$1 = "(?:\\ud83c[\\udde6-\\uddff]){2}", rsSurrPair$1 = "[\\ud800-\\udbff][\\udc00-\\udfff]", rsUpper = "[" + rsUpperRange + "]", rsZWJ$2 = "\\u200d";
var rsMiscLower = "(?:" + rsLower + "|" + rsMisc + ")", rsMiscUpper = "(?:" + rsUpper + "|" + rsMisc + ")", rsOptContrLower = "(?:" + rsApos + "(?:d|ll|m|re|s|t|ve))?", rsOptContrUpper = "(?:" + rsApos + "(?:D|LL|M|RE|S|T|VE))?", reOptMod$1 = rsModifier$1 + "?", rsOptVar$1 = "[" + rsVarRange$2 + "]?", rsOptJoin$1 = "(?:" + rsZWJ$2 + "(?:" + [rsNonAstral$1, rsRegional$1, rsSurrPair$1].join("|") + ")" + rsOptVar$1 + reOptMod$1 + ")*", rsOrdLower = "\\d*(?:1st|2nd|3rd|(?![123])\\dth)(?=\\b|[A-Z_])", rsOrdUpper = "\\d*(?:1ST|2ND|3RD|(?![123])\\dTH)(?=\\b|[a-z_])", rsSeq$1 = rsOptVar$1 + reOptMod$1 + rsOptJoin$1, rsEmoji = "(?:" + [rsDingbat, rsRegional$1, rsSurrPair$1].join("|") + ")" + rsSeq$1;
var reUnicodeWord = RegExp([
  rsUpper + "?" + rsLower + "+" + rsOptContrLower + "(?=" + [rsBreak, rsUpper, "$"].join("|") + ")",
  rsMiscUpper + "+" + rsOptContrUpper + "(?=" + [rsBreak, rsUpper + rsMiscLower, "$"].join("|") + ")",
  rsUpper + "?" + rsMiscLower + "+" + rsOptContrLower,
  rsUpper + "+" + rsOptContrUpper,
  rsOrdUpper,
  rsOrdLower,
  rsDigits,
  rsEmoji
].join("|"), "g");
function unicodeWords(string2) {
  return string2.match(reUnicodeWord) || [];
}
function words(string2, pattern, guard) {
  string2 = toString$2(string2);
  pattern = guard ? void 0 : pattern;
  if (pattern === void 0) {
    return hasUnicodeWord(string2) ? unicodeWords(string2) : asciiWords(string2);
  }
  return string2.match(pattern) || [];
}
var rsApos$1 = "['\u2019]";
var reApos = RegExp(rsApos$1, "g");
function createCompounder(callback) {
  return function(string2) {
    return arrayReduce(words(deburr(string2).replace(reApos, "")), callback, "");
  };
}
var camelCase = createCompounder(function(result2, word, index) {
  word = word.toLowerCase();
  return result2 + (index ? capitalize(word) : word);
});
function castArray() {
  if (!arguments.length) {
    return [];
  }
  var value = arguments[0];
  return isArray$2(value) ? value : [value];
}
var nativeIsFinite = root.isFinite, nativeMin$2 = Math.min;
function createRound(methodName) {
  var func2 = Math[methodName];
  return function(number2, precision) {
    number2 = toNumber(number2);
    precision = precision == null ? 0 : nativeMin$2(toInteger(precision), 292);
    if (precision && nativeIsFinite(number2)) {
      var pair = (toString$2(number2) + "e").split("e"), value = func2(pair[0] + "e" + (+pair[1] + precision));
      pair = (toString$2(value) + "e").split("e");
      return +(pair[0] + "e" + (+pair[1] - precision));
    }
    return func2(number2);
  };
}
var ceil = createRound("ceil");
function chain(value) {
  var result2 = lodash(value);
  result2.__chain__ = true;
  return result2;
}
var nativeCeil = Math.ceil, nativeMax$4 = Math.max;
function chunk(array2, size2, guard) {
  if (guard ? isIterateeCall(array2, size2, guard) : size2 === void 0) {
    size2 = 1;
  } else {
    size2 = nativeMax$4(toInteger(size2), 0);
  }
  var length = array2 == null ? 0 : array2.length;
  if (!length || size2 < 1) {
    return [];
  }
  var index = 0, resIndex = 0, result2 = Array(nativeCeil(length / size2));
  while (index < length) {
    result2[resIndex++] = baseSlice(array2, index, index += size2);
  }
  return result2;
}
function baseClamp(number2, lower, upper) {
  if (number2 === number2) {
    if (upper !== void 0) {
      number2 = number2 <= upper ? number2 : upper;
    }
    if (lower !== void 0) {
      number2 = number2 >= lower ? number2 : lower;
    }
  }
  return number2;
}
function clamp(number2, lower, upper) {
  if (upper === void 0) {
    upper = lower;
    lower = void 0;
  }
  if (upper !== void 0) {
    upper = toNumber(upper);
    upper = upper === upper ? upper : 0;
  }
  if (lower !== void 0) {
    lower = toNumber(lower);
    lower = lower === lower ? lower : 0;
  }
  return baseClamp(toNumber(number2), lower, upper);
}
function stackClear() {
  this.__data__ = new ListCache();
  this.size = 0;
}
function stackDelete(key) {
  var data = this.__data__, result2 = data["delete"](key);
  this.size = data.size;
  return result2;
}
function stackGet(key) {
  return this.__data__.get(key);
}
function stackHas(key) {
  return this.__data__.has(key);
}
var LARGE_ARRAY_SIZE = 200;
function stackSet(key, value) {
  var data = this.__data__;
  if (data instanceof ListCache) {
    var pairs = data.__data__;
    if (!Map$1 || pairs.length < LARGE_ARRAY_SIZE - 1) {
      pairs.push([key, value]);
      this.size = ++data.size;
      return this;
    }
    data = this.__data__ = new MapCache(pairs);
  }
  data.set(key, value);
  this.size = data.size;
  return this;
}
function Stack(entries) {
  var data = this.__data__ = new ListCache(entries);
  this.size = data.size;
}
Stack.prototype.clear = stackClear;
Stack.prototype["delete"] = stackDelete;
Stack.prototype.get = stackGet;
Stack.prototype.has = stackHas;
Stack.prototype.set = stackSet;
function baseAssign(object2, source) {
  return object2 && copyObject(source, keys(source), object2);
}
function baseAssignIn(object2, source) {
  return object2 && copyObject(source, keysIn(source), object2);
}
var freeExports$2 = typeof exports == "object" && exports && !exports.nodeType && exports;
var freeModule$2 = freeExports$2 && typeof module == "object" && module && !module.nodeType && module;
var moduleExports$2 = freeModule$2 && freeModule$2.exports === freeExports$2;
var Buffer$1$1 = moduleExports$2 ? root.Buffer : void 0, allocUnsafe$1 = Buffer$1$1 ? Buffer$1$1.allocUnsafe : void 0;
function cloneBuffer(buffer, isDeep) {
  if (isDeep) {
    return buffer.slice();
  }
  var length = buffer.length, result2 = allocUnsafe$1 ? allocUnsafe$1(length) : new buffer.constructor(length);
  buffer.copy(result2);
  return result2;
}
function arrayFilter(array2, predicate) {
  var index = -1, length = array2 == null ? 0 : array2.length, resIndex = 0, result2 = [];
  while (++index < length) {
    var value = array2[index];
    if (predicate(value, index, array2)) {
      result2[resIndex++] = value;
    }
  }
  return result2;
}
function stubArray() {
  return [];
}
var objectProto$f = Object.prototype;
var propertyIsEnumerable$1 = objectProto$f.propertyIsEnumerable;
var nativeGetSymbols = Object.getOwnPropertySymbols;
var getSymbols = !nativeGetSymbols ? stubArray : function(object2) {
  if (object2 == null) {
    return [];
  }
  object2 = Object(object2);
  return arrayFilter(nativeGetSymbols(object2), function(symbol) {
    return propertyIsEnumerable$1.call(object2, symbol);
  });
};
function copySymbols(source, object2) {
  return copyObject(source, getSymbols(source), object2);
}
var nativeGetSymbols$1 = Object.getOwnPropertySymbols;
var getSymbolsIn = !nativeGetSymbols$1 ? stubArray : function(object2) {
  var result2 = [];
  while (object2) {
    arrayPush(result2, getSymbols(object2));
    object2 = getPrototype(object2);
  }
  return result2;
};
function copySymbolsIn(source, object2) {
  return copyObject(source, getSymbolsIn(source), object2);
}
function baseGetAllKeys(object2, keysFunc, symbolsFunc) {
  var result2 = keysFunc(object2);
  return isArray$2(object2) ? result2 : arrayPush(result2, symbolsFunc(object2));
}
function getAllKeys(object2) {
  return baseGetAllKeys(object2, keys, getSymbols);
}
function getAllKeysIn(object2) {
  return baseGetAllKeys(object2, keysIn, getSymbolsIn);
}
var DataView = getNative(root, "DataView");
var Promise$1 = getNative(root, "Promise");
var Set$1 = getNative(root, "Set");
var mapTag$1 = "[object Map]", objectTag$2 = "[object Object]", promiseTag = "[object Promise]", setTag$1 = "[object Set]", weakMapTag$1 = "[object WeakMap]";
var dataViewTag$1 = "[object DataView]";
var dataViewCtorString = toSource(DataView), mapCtorString = toSource(Map$1), promiseCtorString = toSource(Promise$1), setCtorString = toSource(Set$1), weakMapCtorString = toSource(WeakMap);
var getTag = baseGetTag;
if (DataView && getTag(new DataView(new ArrayBuffer(1))) != dataViewTag$1 || Map$1 && getTag(new Map$1()) != mapTag$1 || Promise$1 && getTag(Promise$1.resolve()) != promiseTag || Set$1 && getTag(new Set$1()) != setTag$1 || WeakMap && getTag(new WeakMap()) != weakMapTag$1) {
  getTag = function(value) {
    var result2 = baseGetTag(value), Ctor = result2 == objectTag$2 ? value.constructor : void 0, ctorString = Ctor ? toSource(Ctor) : "";
    if (ctorString) {
      switch (ctorString) {
        case dataViewCtorString:
          return dataViewTag$1;
        case mapCtorString:
          return mapTag$1;
        case promiseCtorString:
          return promiseTag;
        case setCtorString:
          return setTag$1;
        case weakMapCtorString:
          return weakMapTag$1;
      }
    }
    return result2;
  };
}
var getTag$1 = getTag;
var objectProto$g = Object.prototype;
var hasOwnProperty$d = objectProto$g.hasOwnProperty;
function initCloneArray(array2) {
  var length = array2.length, result2 = new array2.constructor(length);
  if (length && typeof array2[0] == "string" && hasOwnProperty$d.call(array2, "index")) {
    result2.index = array2.index;
    result2.input = array2.input;
  }
  return result2;
}
var Uint8Array$1 = root.Uint8Array;
function cloneArrayBuffer(arrayBuffer) {
  var result2 = new arrayBuffer.constructor(arrayBuffer.byteLength);
  new Uint8Array$1(result2).set(new Uint8Array$1(arrayBuffer));
  return result2;
}
function cloneDataView(dataView, isDeep) {
  var buffer = isDeep ? cloneArrayBuffer(dataView.buffer) : dataView.buffer;
  return new dataView.constructor(buffer, dataView.byteOffset, dataView.byteLength);
}
var reFlags = /\w*$/;
function cloneRegExp(regexp) {
  var result2 = new regexp.constructor(regexp.source, reFlags.exec(regexp));
  result2.lastIndex = regexp.lastIndex;
  return result2;
}
var symbolProto$1 = Symbol$1 ? Symbol$1.prototype : void 0, symbolValueOf = symbolProto$1 ? symbolProto$1.valueOf : void 0;
function cloneSymbol(symbol) {
  return symbolValueOf ? Object(symbolValueOf.call(symbol)) : {};
}
function cloneTypedArray(typedArray, isDeep) {
  var buffer = isDeep ? cloneArrayBuffer(typedArray.buffer) : typedArray.buffer;
  return new typedArray.constructor(buffer, typedArray.byteOffset, typedArray.length);
}
var boolTag$1 = "[object Boolean]", dateTag$1 = "[object Date]", mapTag$2 = "[object Map]", numberTag$1 = "[object Number]", regexpTag$1 = "[object RegExp]", setTag$2 = "[object Set]", stringTag$1 = "[object String]", symbolTag$1 = "[object Symbol]";
var arrayBufferTag$1 = "[object ArrayBuffer]", dataViewTag$2 = "[object DataView]", float32Tag$1 = "[object Float32Array]", float64Tag$1 = "[object Float64Array]", int8Tag$1 = "[object Int8Array]", int16Tag$1 = "[object Int16Array]", int32Tag$1 = "[object Int32Array]", uint8Tag$1 = "[object Uint8Array]", uint8ClampedTag$1 = "[object Uint8ClampedArray]", uint16Tag$1 = "[object Uint16Array]", uint32Tag$1 = "[object Uint32Array]";
function initCloneByTag(object2, tag, isDeep) {
  var Ctor = object2.constructor;
  switch (tag) {
    case arrayBufferTag$1:
      return cloneArrayBuffer(object2);
    case boolTag$1:
    case dateTag$1:
      return new Ctor(+object2);
    case dataViewTag$2:
      return cloneDataView(object2, isDeep);
    case float32Tag$1:
    case float64Tag$1:
    case int8Tag$1:
    case int16Tag$1:
    case int32Tag$1:
    case uint8Tag$1:
    case uint8ClampedTag$1:
    case uint16Tag$1:
    case uint32Tag$1:
      return cloneTypedArray(object2, isDeep);
    case mapTag$2:
      return new Ctor();
    case numberTag$1:
    case stringTag$1:
      return new Ctor(object2);
    case regexpTag$1:
      return cloneRegExp(object2);
    case setTag$2:
      return new Ctor();
    case symbolTag$1:
      return cloneSymbol(object2);
  }
}
function initCloneObject(object2) {
  return typeof object2.constructor == "function" && !isPrototype(object2) ? baseCreate(getPrototype(object2)) : {};
}
var mapTag$3 = "[object Map]";
function baseIsMap(value) {
  return isObjectLike(value) && getTag$1(value) == mapTag$3;
}
var nodeIsMap = nodeUtil && nodeUtil.isMap;
var isMap = nodeIsMap ? baseUnary(nodeIsMap) : baseIsMap;
var setTag$3 = "[object Set]";
function baseIsSet(value) {
  return isObjectLike(value) && getTag$1(value) == setTag$3;
}
var nodeIsSet = nodeUtil && nodeUtil.isSet;
var isSet = nodeIsSet ? baseUnary(nodeIsSet) : baseIsSet;
var CLONE_DEEP_FLAG = 1, CLONE_FLAT_FLAG = 2, CLONE_SYMBOLS_FLAG = 4;
var argsTag$2 = "[object Arguments]", arrayTag$1 = "[object Array]", boolTag$2 = "[object Boolean]", dateTag$2 = "[object Date]", errorTag$2 = "[object Error]", funcTag$2 = "[object Function]", genTag$1 = "[object GeneratorFunction]", mapTag$4 = "[object Map]", numberTag$2 = "[object Number]", objectTag$3 = "[object Object]", regexpTag$2 = "[object RegExp]", setTag$4 = "[object Set]", stringTag$2 = "[object String]", symbolTag$2 = "[object Symbol]", weakMapTag$2 = "[object WeakMap]";
var arrayBufferTag$2 = "[object ArrayBuffer]", dataViewTag$3 = "[object DataView]", float32Tag$2 = "[object Float32Array]", float64Tag$2 = "[object Float64Array]", int8Tag$2 = "[object Int8Array]", int16Tag$2 = "[object Int16Array]", int32Tag$2 = "[object Int32Array]", uint8Tag$2 = "[object Uint8Array]", uint8ClampedTag$2 = "[object Uint8ClampedArray]", uint16Tag$2 = "[object Uint16Array]", uint32Tag$2 = "[object Uint32Array]";
var cloneableTags = {};
cloneableTags[argsTag$2] = cloneableTags[arrayTag$1] = cloneableTags[arrayBufferTag$2] = cloneableTags[dataViewTag$3] = cloneableTags[boolTag$2] = cloneableTags[dateTag$2] = cloneableTags[float32Tag$2] = cloneableTags[float64Tag$2] = cloneableTags[int8Tag$2] = cloneableTags[int16Tag$2] = cloneableTags[int32Tag$2] = cloneableTags[mapTag$4] = cloneableTags[numberTag$2] = cloneableTags[objectTag$3] = cloneableTags[regexpTag$2] = cloneableTags[setTag$4] = cloneableTags[stringTag$2] = cloneableTags[symbolTag$2] = cloneableTags[uint8Tag$2] = cloneableTags[uint8ClampedTag$2] = cloneableTags[uint16Tag$2] = cloneableTags[uint32Tag$2] = true;
cloneableTags[errorTag$2] = cloneableTags[funcTag$2] = cloneableTags[weakMapTag$2] = false;
function baseClone(value, bitmask, customizer, key, object2, stack) {
  var result2, isDeep = bitmask & CLONE_DEEP_FLAG, isFlat = bitmask & CLONE_FLAT_FLAG, isFull = bitmask & CLONE_SYMBOLS_FLAG;
  if (customizer) {
    result2 = object2 ? customizer(value, key, object2, stack) : customizer(value);
  }
  if (result2 !== void 0) {
    return result2;
  }
  if (!isObject$1(value)) {
    return value;
  }
  var isArr = isArray$2(value);
  if (isArr) {
    result2 = initCloneArray(value);
    if (!isDeep) {
      return copyArray(value, result2);
    }
  } else {
    var tag = getTag$1(value), isFunc = tag == funcTag$2 || tag == genTag$1;
    if (isBuffer$2(value)) {
      return cloneBuffer(value, isDeep);
    }
    if (tag == objectTag$3 || tag == argsTag$2 || isFunc && !object2) {
      result2 = isFlat || isFunc ? {} : initCloneObject(value);
      if (!isDeep) {
        return isFlat ? copySymbolsIn(value, baseAssignIn(result2, value)) : copySymbols(value, baseAssign(result2, value));
      }
    } else {
      if (!cloneableTags[tag]) {
        return object2 ? value : {};
      }
      result2 = initCloneByTag(value, tag, isDeep);
    }
  }
  stack || (stack = new Stack());
  var stacked = stack.get(value);
  if (stacked) {
    return stacked;
  }
  stack.set(value, result2);
  if (isSet(value)) {
    value.forEach(function(subValue) {
      result2.add(baseClone(subValue, bitmask, customizer, subValue, value, stack));
    });
  } else if (isMap(value)) {
    value.forEach(function(subValue, key2) {
      result2.set(key2, baseClone(subValue, bitmask, customizer, key2, value, stack));
    });
  }
  var keysFunc = isFull ? isFlat ? getAllKeysIn : getAllKeys : isFlat ? keysIn : keys;
  var props = isArr ? void 0 : keysFunc(value);
  arrayEach(props || value, function(subValue, key2) {
    if (props) {
      key2 = subValue;
      subValue = value[key2];
    }
    assignValue(result2, key2, baseClone(subValue, bitmask, customizer, key2, value, stack));
  });
  return result2;
}
var CLONE_SYMBOLS_FLAG$1 = 4;
function clone(value) {
  return baseClone(value, CLONE_SYMBOLS_FLAG$1);
}
var CLONE_DEEP_FLAG$1 = 1, CLONE_SYMBOLS_FLAG$2 = 4;
function cloneDeep(value) {
  return baseClone(value, CLONE_DEEP_FLAG$1 | CLONE_SYMBOLS_FLAG$2);
}
var CLONE_DEEP_FLAG$2 = 1, CLONE_SYMBOLS_FLAG$3 = 4;
function cloneDeepWith(value, customizer) {
  customizer = typeof customizer == "function" ? customizer : void 0;
  return baseClone(value, CLONE_DEEP_FLAG$2 | CLONE_SYMBOLS_FLAG$3, customizer);
}
var CLONE_SYMBOLS_FLAG$4 = 4;
function cloneWith(value, customizer) {
  customizer = typeof customizer == "function" ? customizer : void 0;
  return baseClone(value, CLONE_SYMBOLS_FLAG$4, customizer);
}
function wrapperCommit() {
  return new LodashWrapper(this.value(), this.__chain__);
}
function compact(array2) {
  var index = -1, length = array2 == null ? 0 : array2.length, resIndex = 0, result2 = [];
  while (++index < length) {
    var value = array2[index];
    if (value) {
      result2[resIndex++] = value;
    }
  }
  return result2;
}
function concat() {
  var length = arguments.length;
  if (!length) {
    return [];
  }
  var args = Array(length - 1), array2 = arguments[0], index = length;
  while (index--) {
    args[index - 1] = arguments[index];
  }
  return arrayPush(isArray$2(array2) ? copyArray(array2) : [array2], baseFlatten(args, 1));
}
var HASH_UNDEFINED$2 = "__lodash_hash_undefined__";
function setCacheAdd(value) {
  this.__data__.set(value, HASH_UNDEFINED$2);
  return this;
}
function setCacheHas(value) {
  return this.__data__.has(value);
}
function SetCache(values2) {
  var index = -1, length = values2 == null ? 0 : values2.length;
  this.__data__ = new MapCache();
  while (++index < length) {
    this.add(values2[index]);
  }
}
SetCache.prototype.add = SetCache.prototype.push = setCacheAdd;
SetCache.prototype.has = setCacheHas;
function arraySome(array2, predicate) {
  var index = -1, length = array2 == null ? 0 : array2.length;
  while (++index < length) {
    if (predicate(array2[index], index, array2)) {
      return true;
    }
  }
  return false;
}
function cacheHas(cache, key) {
  return cache.has(key);
}
var COMPARE_PARTIAL_FLAG = 1, COMPARE_UNORDERED_FLAG = 2;
function equalArrays(array2, other, bitmask, customizer, equalFunc, stack) {
  var isPartial = bitmask & COMPARE_PARTIAL_FLAG, arrLength = array2.length, othLength = other.length;
  if (arrLength != othLength && !(isPartial && othLength > arrLength)) {
    return false;
  }
  var arrStacked = stack.get(array2);
  var othStacked = stack.get(other);
  if (arrStacked && othStacked) {
    return arrStacked == other && othStacked == array2;
  }
  var index = -1, result2 = true, seen = bitmask & COMPARE_UNORDERED_FLAG ? new SetCache() : void 0;
  stack.set(array2, other);
  stack.set(other, array2);
  while (++index < arrLength) {
    var arrValue = array2[index], othValue = other[index];
    if (customizer) {
      var compared = isPartial ? customizer(othValue, arrValue, index, other, array2, stack) : customizer(arrValue, othValue, index, array2, other, stack);
    }
    if (compared !== void 0) {
      if (compared) {
        continue;
      }
      result2 = false;
      break;
    }
    if (seen) {
      if (!arraySome(other, function(othValue2, othIndex) {
        if (!cacheHas(seen, othIndex) && (arrValue === othValue2 || equalFunc(arrValue, othValue2, bitmask, customizer, stack))) {
          return seen.push(othIndex);
        }
      })) {
        result2 = false;
        break;
      }
    } else if (!(arrValue === othValue || equalFunc(arrValue, othValue, bitmask, customizer, stack))) {
      result2 = false;
      break;
    }
  }
  stack["delete"](array2);
  stack["delete"](other);
  return result2;
}
function mapToArray(map2) {
  var index = -1, result2 = Array(map2.size);
  map2.forEach(function(value, key) {
    result2[++index] = [key, value];
  });
  return result2;
}
function setToArray(set2) {
  var index = -1, result2 = Array(set2.size);
  set2.forEach(function(value) {
    result2[++index] = value;
  });
  return result2;
}
var COMPARE_PARTIAL_FLAG$1 = 1, COMPARE_UNORDERED_FLAG$1 = 2;
var boolTag$3 = "[object Boolean]", dateTag$3 = "[object Date]", errorTag$3 = "[object Error]", mapTag$5 = "[object Map]", numberTag$3 = "[object Number]", regexpTag$3 = "[object RegExp]", setTag$5 = "[object Set]", stringTag$3 = "[object String]", symbolTag$3 = "[object Symbol]";
var arrayBufferTag$3 = "[object ArrayBuffer]", dataViewTag$4 = "[object DataView]";
var symbolProto$2 = Symbol$1 ? Symbol$1.prototype : void 0, symbolValueOf$1 = symbolProto$2 ? symbolProto$2.valueOf : void 0;
function equalByTag(object2, other, tag, bitmask, customizer, equalFunc, stack) {
  switch (tag) {
    case dataViewTag$4:
      if (object2.byteLength != other.byteLength || object2.byteOffset != other.byteOffset) {
        return false;
      }
      object2 = object2.buffer;
      other = other.buffer;
    case arrayBufferTag$3:
      if (object2.byteLength != other.byteLength || !equalFunc(new Uint8Array$1(object2), new Uint8Array$1(other))) {
        return false;
      }
      return true;
    case boolTag$3:
    case dateTag$3:
    case numberTag$3:
      return eq(+object2, +other);
    case errorTag$3:
      return object2.name == other.name && object2.message == other.message;
    case regexpTag$3:
    case stringTag$3:
      return object2 == other + "";
    case mapTag$5:
      var convert = mapToArray;
    case setTag$5:
      var isPartial = bitmask & COMPARE_PARTIAL_FLAG$1;
      convert || (convert = setToArray);
      if (object2.size != other.size && !isPartial) {
        return false;
      }
      var stacked = stack.get(object2);
      if (stacked) {
        return stacked == other;
      }
      bitmask |= COMPARE_UNORDERED_FLAG$1;
      stack.set(object2, other);
      var result2 = equalArrays(convert(object2), convert(other), bitmask, customizer, equalFunc, stack);
      stack["delete"](object2);
      return result2;
    case symbolTag$3:
      if (symbolValueOf$1) {
        return symbolValueOf$1.call(object2) == symbolValueOf$1.call(other);
      }
  }
  return false;
}
var COMPARE_PARTIAL_FLAG$2 = 1;
var objectProto$h = Object.prototype;
var hasOwnProperty$e = objectProto$h.hasOwnProperty;
function equalObjects(object2, other, bitmask, customizer, equalFunc, stack) {
  var isPartial = bitmask & COMPARE_PARTIAL_FLAG$2, objProps = getAllKeys(object2), objLength = objProps.length, othProps = getAllKeys(other), othLength = othProps.length;
  if (objLength != othLength && !isPartial) {
    return false;
  }
  var index = objLength;
  while (index--) {
    var key = objProps[index];
    if (!(isPartial ? key in other : hasOwnProperty$e.call(other, key))) {
      return false;
    }
  }
  var objStacked = stack.get(object2);
  var othStacked = stack.get(other);
  if (objStacked && othStacked) {
    return objStacked == other && othStacked == object2;
  }
  var result2 = true;
  stack.set(object2, other);
  stack.set(other, object2);
  var skipCtor = isPartial;
  while (++index < objLength) {
    key = objProps[index];
    var objValue = object2[key], othValue = other[key];
    if (customizer) {
      var compared = isPartial ? customizer(othValue, objValue, key, other, object2, stack) : customizer(objValue, othValue, key, object2, other, stack);
    }
    if (!(compared === void 0 ? objValue === othValue || equalFunc(objValue, othValue, bitmask, customizer, stack) : compared)) {
      result2 = false;
      break;
    }
    skipCtor || (skipCtor = key == "constructor");
  }
  if (result2 && !skipCtor) {
    var objCtor = object2.constructor, othCtor = other.constructor;
    if (objCtor != othCtor && ("constructor" in object2 && "constructor" in other) && !(typeof objCtor == "function" && objCtor instanceof objCtor && typeof othCtor == "function" && othCtor instanceof othCtor)) {
      result2 = false;
    }
  }
  stack["delete"](object2);
  stack["delete"](other);
  return result2;
}
var COMPARE_PARTIAL_FLAG$3 = 1;
var argsTag$3 = "[object Arguments]", arrayTag$2 = "[object Array]", objectTag$4 = "[object Object]";
var objectProto$i = Object.prototype;
var hasOwnProperty$f = objectProto$i.hasOwnProperty;
function baseIsEqualDeep(object2, other, bitmask, customizer, equalFunc, stack) {
  var objIsArr = isArray$2(object2), othIsArr = isArray$2(other), objTag = objIsArr ? arrayTag$2 : getTag$1(object2), othTag = othIsArr ? arrayTag$2 : getTag$1(other);
  objTag = objTag == argsTag$3 ? objectTag$4 : objTag;
  othTag = othTag == argsTag$3 ? objectTag$4 : othTag;
  var objIsObj = objTag == objectTag$4, othIsObj = othTag == objectTag$4, isSameTag = objTag == othTag;
  if (isSameTag && isBuffer$2(object2)) {
    if (!isBuffer$2(other)) {
      return false;
    }
    objIsArr = true;
    objIsObj = false;
  }
  if (isSameTag && !objIsObj) {
    stack || (stack = new Stack());
    return objIsArr || isTypedArray$1(object2) ? equalArrays(object2, other, bitmask, customizer, equalFunc, stack) : equalByTag(object2, other, objTag, bitmask, customizer, equalFunc, stack);
  }
  if (!(bitmask & COMPARE_PARTIAL_FLAG$3)) {
    var objIsWrapped = objIsObj && hasOwnProperty$f.call(object2, "__wrapped__"), othIsWrapped = othIsObj && hasOwnProperty$f.call(other, "__wrapped__");
    if (objIsWrapped || othIsWrapped) {
      var objUnwrapped = objIsWrapped ? object2.value() : object2, othUnwrapped = othIsWrapped ? other.value() : other;
      stack || (stack = new Stack());
      return equalFunc(objUnwrapped, othUnwrapped, bitmask, customizer, stack);
    }
  }
  if (!isSameTag) {
    return false;
  }
  stack || (stack = new Stack());
  return equalObjects(object2, other, bitmask, customizer, equalFunc, stack);
}
function baseIsEqual(value, other, bitmask, customizer, stack) {
  if (value === other) {
    return true;
  }
  if (value == null || other == null || !isObjectLike(value) && !isObjectLike(other)) {
    return value !== value && other !== other;
  }
  return baseIsEqualDeep(value, other, bitmask, customizer, baseIsEqual, stack);
}
var COMPARE_PARTIAL_FLAG$4 = 1, COMPARE_UNORDERED_FLAG$2 = 2;
function baseIsMatch(object2, source, matchData, customizer) {
  var index = matchData.length, length = index, noCustomizer = !customizer;
  if (object2 == null) {
    return !length;
  }
  object2 = Object(object2);
  while (index--) {
    var data = matchData[index];
    if (noCustomizer && data[2] ? data[1] !== object2[data[0]] : !(data[0] in object2)) {
      return false;
    }
  }
  while (++index < length) {
    data = matchData[index];
    var key = data[0], objValue = object2[key], srcValue = data[1];
    if (noCustomizer && data[2]) {
      if (objValue === void 0 && !(key in object2)) {
        return false;
      }
    } else {
      var stack = new Stack();
      if (customizer) {
        var result2 = customizer(objValue, srcValue, key, object2, source, stack);
      }
      if (!(result2 === void 0 ? baseIsEqual(srcValue, objValue, COMPARE_PARTIAL_FLAG$4 | COMPARE_UNORDERED_FLAG$2, customizer, stack) : result2)) {
        return false;
      }
    }
  }
  return true;
}
function isStrictComparable(value) {
  return value === value && !isObject$1(value);
}
function getMatchData(object2) {
  var result2 = keys(object2), length = result2.length;
  while (length--) {
    var key = result2[length], value = object2[key];
    result2[length] = [key, value, isStrictComparable(value)];
  }
  return result2;
}
function matchesStrictComparable(key, srcValue) {
  return function(object2) {
    if (object2 == null) {
      return false;
    }
    return object2[key] === srcValue && (srcValue !== void 0 || key in Object(object2));
  };
}
function baseMatches(source) {
  var matchData = getMatchData(source);
  if (matchData.length == 1 && matchData[0][2]) {
    return matchesStrictComparable(matchData[0][0], matchData[0][1]);
  }
  return function(object2) {
    return object2 === source || baseIsMatch(object2, source, matchData);
  };
}
function baseHasIn(object2, key) {
  return object2 != null && key in Object(object2);
}
function hasPath(object2, path, hasFunc) {
  path = castPath(path, object2);
  var index = -1, length = path.length, result2 = false;
  while (++index < length) {
    var key = toKey(path[index]);
    if (!(result2 = object2 != null && hasFunc(object2, key))) {
      break;
    }
    object2 = object2[key];
  }
  if (result2 || ++index != length) {
    return result2;
  }
  length = object2 == null ? 0 : object2.length;
  return !!length && isLength(length) && isIndex(key, length) && (isArray$2(object2) || isArguments(object2));
}
function hasIn(object2, path) {
  return object2 != null && hasPath(object2, path, baseHasIn);
}
var COMPARE_PARTIAL_FLAG$5 = 1, COMPARE_UNORDERED_FLAG$3 = 2;
function baseMatchesProperty(path, srcValue) {
  if (isKey(path) && isStrictComparable(srcValue)) {
    return matchesStrictComparable(toKey(path), srcValue);
  }
  return function(object2) {
    var objValue = get(object2, path);
    return objValue === void 0 && objValue === srcValue ? hasIn(object2, path) : baseIsEqual(srcValue, objValue, COMPARE_PARTIAL_FLAG$5 | COMPARE_UNORDERED_FLAG$3);
  };
}
function baseProperty(key) {
  return function(object2) {
    return object2 == null ? void 0 : object2[key];
  };
}
function basePropertyDeep(path) {
  return function(object2) {
    return baseGet(object2, path);
  };
}
function property(path) {
  return isKey(path) ? baseProperty(toKey(path)) : basePropertyDeep(path);
}
function baseIteratee(value) {
  if (typeof value == "function") {
    return value;
  }
  if (value == null) {
    return identity$1;
  }
  if (typeof value == "object") {
    return isArray$2(value) ? baseMatchesProperty(value[0], value[1]) : baseMatches(value);
  }
  return property(value);
}
var FUNC_ERROR_TEXT$4 = "Expected a function";
function cond(pairs) {
  var length = pairs == null ? 0 : pairs.length, toIteratee = baseIteratee;
  pairs = !length ? [] : arrayMap(pairs, function(pair) {
    if (typeof pair[1] != "function") {
      throw new TypeError(FUNC_ERROR_TEXT$4);
    }
    return [toIteratee(pair[0]), pair[1]];
  });
  return baseRest(function(args) {
    var index = -1;
    while (++index < length) {
      var pair = pairs[index];
      if (apply(pair[0], this, args)) {
        return apply(pair[1], this, args);
      }
    }
  });
}
function baseConformsTo(object2, source, props) {
  var length = props.length;
  if (object2 == null) {
    return !length;
  }
  object2 = Object(object2);
  while (length--) {
    var key = props[length], predicate = source[key], value = object2[key];
    if (value === void 0 && !(key in object2) || !predicate(value)) {
      return false;
    }
  }
  return true;
}
function baseConforms(source) {
  var props = keys(source);
  return function(object2) {
    return baseConformsTo(object2, source, props);
  };
}
var CLONE_DEEP_FLAG$3 = 1;
function conforms(source) {
  return baseConforms(baseClone(source, CLONE_DEEP_FLAG$3));
}
function conformsTo(object2, source) {
  return source == null || baseConformsTo(object2, source, keys(source));
}
function arrayAggregator(array2, setter, iteratee2, accumulator) {
  var index = -1, length = array2 == null ? 0 : array2.length;
  while (++index < length) {
    var value = array2[index];
    setter(accumulator, value, iteratee2(value), array2);
  }
  return accumulator;
}
function createBaseFor(fromRight) {
  return function(object2, iteratee2, keysFunc) {
    var index = -1, iterable = Object(object2), props = keysFunc(object2), length = props.length;
    while (length--) {
      var key = props[fromRight ? length : ++index];
      if (iteratee2(iterable[key], key, iterable) === false) {
        break;
      }
    }
    return object2;
  };
}
var baseFor = createBaseFor();
function baseForOwn(object2, iteratee2) {
  return object2 && baseFor(object2, iteratee2, keys);
}
function createBaseEach(eachFunc, fromRight) {
  return function(collection2, iteratee2) {
    if (collection2 == null) {
      return collection2;
    }
    if (!isArrayLike(collection2)) {
      return eachFunc(collection2, iteratee2);
    }
    var length = collection2.length, index = fromRight ? length : -1, iterable = Object(collection2);
    while (fromRight ? index-- : ++index < length) {
      if (iteratee2(iterable[index], index, iterable) === false) {
        break;
      }
    }
    return collection2;
  };
}
var baseEach = createBaseEach(baseForOwn);
function baseAggregator(collection2, setter, iteratee2, accumulator) {
  baseEach(collection2, function(value, key, collection3) {
    setter(accumulator, value, iteratee2(value), collection3);
  });
  return accumulator;
}
function createAggregator(setter, initializer) {
  return function(collection2, iteratee2) {
    var func2 = isArray$2(collection2) ? arrayAggregator : baseAggregator, accumulator = initializer ? initializer() : {};
    return func2(collection2, setter, baseIteratee(iteratee2), accumulator);
  };
}
var objectProto$j = Object.prototype;
var hasOwnProperty$g = objectProto$j.hasOwnProperty;
var countBy = createAggregator(function(result2, value, key) {
  if (hasOwnProperty$g.call(result2, key)) {
    ++result2[key];
  } else {
    baseAssignValue(result2, key, 1);
  }
});
function create(prototype, properties) {
  var result2 = baseCreate(prototype);
  return properties == null ? result2 : baseAssign(result2, properties);
}
var WRAP_CURRY_FLAG$5 = 8;
function curry(func2, arity, guard) {
  arity = guard ? void 0 : arity;
  var result2 = createWrap(func2, WRAP_CURRY_FLAG$5, void 0, void 0, void 0, void 0, void 0, arity);
  result2.placeholder = curry.placeholder;
  return result2;
}
curry.placeholder = {};
var WRAP_CURRY_RIGHT_FLAG$3 = 16;
function curryRight(func2, arity, guard) {
  arity = guard ? void 0 : arity;
  var result2 = createWrap(func2, WRAP_CURRY_RIGHT_FLAG$3, void 0, void 0, void 0, void 0, void 0, arity);
  result2.placeholder = curryRight.placeholder;
  return result2;
}
curryRight.placeholder = {};
var now$1 = function() {
  return root.Date.now();
};
var FUNC_ERROR_TEXT$5 = "Expected a function";
var nativeMax$5 = Math.max, nativeMin$3 = Math.min;
function debounce(func2, wait, options) {
  var lastArgs, lastThis, maxWait, result2, timerId, lastCallTime, lastInvokeTime = 0, leading = false, maxing = false, trailing = true;
  if (typeof func2 != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$5);
  }
  wait = toNumber(wait) || 0;
  if (isObject$1(options)) {
    leading = !!options.leading;
    maxing = "maxWait" in options;
    maxWait = maxing ? nativeMax$5(toNumber(options.maxWait) || 0, wait) : maxWait;
    trailing = "trailing" in options ? !!options.trailing : trailing;
  }
  function invokeFunc(time) {
    var args = lastArgs, thisArg = lastThis;
    lastArgs = lastThis = void 0;
    lastInvokeTime = time;
    result2 = func2.apply(thisArg, args);
    return result2;
  }
  function leadingEdge(time) {
    lastInvokeTime = time;
    timerId = setTimeout(timerExpired, wait);
    return leading ? invokeFunc(time) : result2;
  }
  function remainingWait(time) {
    var timeSinceLastCall = time - lastCallTime, timeSinceLastInvoke = time - lastInvokeTime, timeWaiting = wait - timeSinceLastCall;
    return maxing ? nativeMin$3(timeWaiting, maxWait - timeSinceLastInvoke) : timeWaiting;
  }
  function shouldInvoke(time) {
    var timeSinceLastCall = time - lastCallTime, timeSinceLastInvoke = time - lastInvokeTime;
    return lastCallTime === void 0 || timeSinceLastCall >= wait || timeSinceLastCall < 0 || maxing && timeSinceLastInvoke >= maxWait;
  }
  function timerExpired() {
    var time = now$1();
    if (shouldInvoke(time)) {
      return trailingEdge(time);
    }
    timerId = setTimeout(timerExpired, remainingWait(time));
  }
  function trailingEdge(time) {
    timerId = void 0;
    if (trailing && lastArgs) {
      return invokeFunc(time);
    }
    lastArgs = lastThis = void 0;
    return result2;
  }
  function cancel() {
    if (timerId !== void 0) {
      clearTimeout(timerId);
    }
    lastInvokeTime = 0;
    lastArgs = lastCallTime = lastThis = timerId = void 0;
  }
  function flush() {
    return timerId === void 0 ? result2 : trailingEdge(now$1());
  }
  function debounced() {
    var time = now$1(), isInvoking = shouldInvoke(time);
    lastArgs = arguments;
    lastThis = this;
    lastCallTime = time;
    if (isInvoking) {
      if (timerId === void 0) {
        return leadingEdge(lastCallTime);
      }
      if (maxing) {
        clearTimeout(timerId);
        timerId = setTimeout(timerExpired, wait);
        return invokeFunc(lastCallTime);
      }
    }
    if (timerId === void 0) {
      timerId = setTimeout(timerExpired, wait);
    }
    return result2;
  }
  debounced.cancel = cancel;
  debounced.flush = flush;
  return debounced;
}
function defaultTo(value, defaultValue) {
  return value == null || value !== value ? defaultValue : value;
}
var objectProto$k = Object.prototype;
var hasOwnProperty$h = objectProto$k.hasOwnProperty;
var defaults$1 = baseRest(function(object2, sources) {
  object2 = Object(object2);
  var index = -1;
  var length = sources.length;
  var guard = length > 2 ? sources[2] : void 0;
  if (guard && isIterateeCall(sources[0], sources[1], guard)) {
    length = 1;
  }
  while (++index < length) {
    var source = sources[index];
    var props = keysIn(source);
    var propsIndex = -1;
    var propsLength = props.length;
    while (++propsIndex < propsLength) {
      var key = props[propsIndex];
      var value = object2[key];
      if (value === void 0 || eq(value, objectProto$k[key]) && !hasOwnProperty$h.call(object2, key)) {
        object2[key] = source[key];
      }
    }
  }
  return object2;
});
function assignMergeValue(object2, key, value) {
  if (value !== void 0 && !eq(object2[key], value) || value === void 0 && !(key in object2)) {
    baseAssignValue(object2, key, value);
  }
}
function isArrayLikeObject(value) {
  return isObjectLike(value) && isArrayLike(value);
}
function safeGet(object2, key) {
  if (key === "constructor" && typeof object2[key] === "function") {
    return;
  }
  if (key == "__proto__") {
    return;
  }
  return object2[key];
}
function toPlainObject(value) {
  return copyObject(value, keysIn(value));
}
function baseMergeDeep(object2, source, key, srcIndex, mergeFunc, customizer, stack) {
  var objValue = safeGet(object2, key), srcValue = safeGet(source, key), stacked = stack.get(srcValue);
  if (stacked) {
    assignMergeValue(object2, key, stacked);
    return;
  }
  var newValue = customizer ? customizer(objValue, srcValue, key + "", object2, source, stack) : void 0;
  var isCommon = newValue === void 0;
  if (isCommon) {
    var isArr = isArray$2(srcValue), isBuff = !isArr && isBuffer$2(srcValue), isTyped = !isArr && !isBuff && isTypedArray$1(srcValue);
    newValue = srcValue;
    if (isArr || isBuff || isTyped) {
      if (isArray$2(objValue)) {
        newValue = objValue;
      } else if (isArrayLikeObject(objValue)) {
        newValue = copyArray(objValue);
      } else if (isBuff) {
        isCommon = false;
        newValue = cloneBuffer(srcValue, true);
      } else if (isTyped) {
        isCommon = false;
        newValue = cloneTypedArray(srcValue, true);
      } else {
        newValue = [];
      }
    } else if (isPlainObject$1(srcValue) || isArguments(srcValue)) {
      newValue = objValue;
      if (isArguments(objValue)) {
        newValue = toPlainObject(objValue);
      } else if (!isObject$1(objValue) || isFunction$1(objValue)) {
        newValue = initCloneObject(srcValue);
      }
    } else {
      isCommon = false;
    }
  }
  if (isCommon) {
    stack.set(srcValue, newValue);
    mergeFunc(newValue, srcValue, srcIndex, customizer, stack);
    stack["delete"](srcValue);
  }
  assignMergeValue(object2, key, newValue);
}
function baseMerge(object2, source, srcIndex, customizer, stack) {
  if (object2 === source) {
    return;
  }
  baseFor(source, function(srcValue, key) {
    stack || (stack = new Stack());
    if (isObject$1(srcValue)) {
      baseMergeDeep(object2, source, key, srcIndex, baseMerge, customizer, stack);
    } else {
      var newValue = customizer ? customizer(safeGet(object2, key), srcValue, key + "", object2, source, stack) : void 0;
      if (newValue === void 0) {
        newValue = srcValue;
      }
      assignMergeValue(object2, key, newValue);
    }
  }, keysIn);
}
function customDefaultsMerge(objValue, srcValue, key, object2, source, stack) {
  if (isObject$1(objValue) && isObject$1(srcValue)) {
    stack.set(srcValue, objValue);
    baseMerge(objValue, srcValue, void 0, customDefaultsMerge, stack);
    stack["delete"](srcValue);
  }
  return objValue;
}
var mergeWith = createAssigner(function(object2, source, srcIndex, customizer) {
  baseMerge(object2, source, srcIndex, customizer);
});
var defaultsDeep = baseRest(function(args) {
  args.push(void 0, customDefaultsMerge);
  return apply(mergeWith, void 0, args);
});
var FUNC_ERROR_TEXT$6 = "Expected a function";
function baseDelay(func2, wait, args) {
  if (typeof func2 != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$6);
  }
  return setTimeout(function() {
    func2.apply(void 0, args);
  }, wait);
}
var defer = baseRest(function(func2, args) {
  return baseDelay(func2, 1, args);
});
var delay = baseRest(function(func2, wait, args) {
  return baseDelay(func2, toNumber(wait) || 0, args);
});
function arrayIncludesWith(array2, value, comparator) {
  var index = -1, length = array2 == null ? 0 : array2.length;
  while (++index < length) {
    if (comparator(value, array2[index])) {
      return true;
    }
  }
  return false;
}
var LARGE_ARRAY_SIZE$1 = 200;
function baseDifference(array2, values2, iteratee2, comparator) {
  var index = -1, includes2 = arrayIncludes, isCommon = true, length = array2.length, result2 = [], valuesLength = values2.length;
  if (!length) {
    return result2;
  }
  if (iteratee2) {
    values2 = arrayMap(values2, baseUnary(iteratee2));
  }
  if (comparator) {
    includes2 = arrayIncludesWith;
    isCommon = false;
  } else if (values2.length >= LARGE_ARRAY_SIZE$1) {
    includes2 = cacheHas;
    isCommon = false;
    values2 = new SetCache(values2);
  }
  outer:
    while (++index < length) {
      var value = array2[index], computed = iteratee2 == null ? value : iteratee2(value);
      value = comparator || value !== 0 ? value : 0;
      if (isCommon && computed === computed) {
        var valuesIndex = valuesLength;
        while (valuesIndex--) {
          if (values2[valuesIndex] === computed) {
            continue outer;
          }
        }
        result2.push(value);
      } else if (!includes2(values2, computed, comparator)) {
        result2.push(value);
      }
    }
  return result2;
}
var difference = baseRest(function(array2, values2) {
  return isArrayLikeObject(array2) ? baseDifference(array2, baseFlatten(values2, 1, isArrayLikeObject, true)) : [];
});
function last(array2) {
  var length = array2 == null ? 0 : array2.length;
  return length ? array2[length - 1] : void 0;
}
var differenceBy = baseRest(function(array2, values2) {
  var iteratee2 = last(values2);
  if (isArrayLikeObject(iteratee2)) {
    iteratee2 = void 0;
  }
  return isArrayLikeObject(array2) ? baseDifference(array2, baseFlatten(values2, 1, isArrayLikeObject, true), baseIteratee(iteratee2)) : [];
});
var differenceWith = baseRest(function(array2, values2) {
  var comparator = last(values2);
  if (isArrayLikeObject(comparator)) {
    comparator = void 0;
  }
  return isArrayLikeObject(array2) ? baseDifference(array2, baseFlatten(values2, 1, isArrayLikeObject, true), void 0, comparator) : [];
});
var divide = createMathOperation(function(dividend, divisor) {
  return dividend / divisor;
}, 1);
function drop(array2, n, guard) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return [];
  }
  n = guard || n === void 0 ? 1 : toInteger(n);
  return baseSlice(array2, n < 0 ? 0 : n, length);
}
function dropRight(array2, n, guard) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return [];
  }
  n = guard || n === void 0 ? 1 : toInteger(n);
  n = length - n;
  return baseSlice(array2, 0, n < 0 ? 0 : n);
}
function baseWhile(array2, predicate, isDrop, fromRight) {
  var length = array2.length, index = fromRight ? length : -1;
  while ((fromRight ? index-- : ++index < length) && predicate(array2[index], index, array2)) {
  }
  return isDrop ? baseSlice(array2, fromRight ? 0 : index, fromRight ? index + 1 : length) : baseSlice(array2, fromRight ? index + 1 : 0, fromRight ? length : index);
}
function dropRightWhile(array2, predicate) {
  return array2 && array2.length ? baseWhile(array2, baseIteratee(predicate), true, true) : [];
}
function dropWhile(array2, predicate) {
  return array2 && array2.length ? baseWhile(array2, baseIteratee(predicate), true) : [];
}
function castFunction(value) {
  return typeof value == "function" ? value : identity$1;
}
function forEach$1(collection2, iteratee2) {
  var func2 = isArray$2(collection2) ? arrayEach : baseEach;
  return func2(collection2, castFunction(iteratee2));
}
function arrayEachRight(array2, iteratee2) {
  var length = array2 == null ? 0 : array2.length;
  while (length--) {
    if (iteratee2(array2[length], length, array2) === false) {
      break;
    }
  }
  return array2;
}
var baseForRight = createBaseFor(true);
function baseForOwnRight(object2, iteratee2) {
  return object2 && baseForRight(object2, iteratee2, keys);
}
var baseEachRight = createBaseEach(baseForOwnRight, true);
function forEachRight(collection2, iteratee2) {
  var func2 = isArray$2(collection2) ? arrayEachRight : baseEachRight;
  return func2(collection2, castFunction(iteratee2));
}
function endsWith$1(string2, target, position) {
  string2 = toString$2(string2);
  target = baseToString(target);
  var length = string2.length;
  position = position === void 0 ? length : baseClamp(toInteger(position), 0, length);
  var end = position;
  position -= target.length;
  return position >= 0 && string2.slice(position, end) == target;
}
function baseToPairs(object2, props) {
  return arrayMap(props, function(key) {
    return [key, object2[key]];
  });
}
function setToPairs(set2) {
  var index = -1, result2 = Array(set2.size);
  set2.forEach(function(value) {
    result2[++index] = [value, value];
  });
  return result2;
}
var mapTag$6 = "[object Map]", setTag$6 = "[object Set]";
function createToPairs(keysFunc) {
  return function(object2) {
    var tag = getTag$1(object2);
    if (tag == mapTag$6) {
      return mapToArray(object2);
    }
    if (tag == setTag$6) {
      return setToPairs(object2);
    }
    return baseToPairs(object2, keysFunc(object2));
  };
}
var toPairs = createToPairs(keys);
var toPairsIn = createToPairs(keysIn);
var htmlEscapes = {
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;",
  '"': "&quot;",
  "'": "&#39;"
};
var escapeHtmlChar = basePropertyOf(htmlEscapes);
var reUnescapedHtml = /[&<>"']/g, reHasUnescapedHtml = RegExp(reUnescapedHtml.source);
function escape(string2) {
  string2 = toString$2(string2);
  return string2 && reHasUnescapedHtml.test(string2) ? string2.replace(reUnescapedHtml, escapeHtmlChar) : string2;
}
var reRegExpChar$1 = /[\\^$.*+?()[\]{}|]/g, reHasRegExpChar = RegExp(reRegExpChar$1.source);
function escapeRegExp(string2) {
  string2 = toString$2(string2);
  return string2 && reHasRegExpChar.test(string2) ? string2.replace(reRegExpChar$1, "\\$&") : string2;
}
function arrayEvery(array2, predicate) {
  var index = -1, length = array2 == null ? 0 : array2.length;
  while (++index < length) {
    if (!predicate(array2[index], index, array2)) {
      return false;
    }
  }
  return true;
}
function baseEvery(collection2, predicate) {
  var result2 = true;
  baseEach(collection2, function(value, index, collection3) {
    result2 = !!predicate(value, index, collection3);
    return result2;
  });
  return result2;
}
function every(collection2, predicate, guard) {
  var func2 = isArray$2(collection2) ? arrayEvery : baseEvery;
  if (guard && isIterateeCall(collection2, predicate, guard)) {
    predicate = void 0;
  }
  return func2(collection2, baseIteratee(predicate));
}
var MAX_ARRAY_LENGTH$1 = 4294967295;
function toLength(value) {
  return value ? baseClamp(toInteger(value), 0, MAX_ARRAY_LENGTH$1) : 0;
}
function baseFill(array2, value, start, end) {
  var length = array2.length;
  start = toInteger(start);
  if (start < 0) {
    start = -start > length ? 0 : length + start;
  }
  end = end === void 0 || end > length ? length : toInteger(end);
  if (end < 0) {
    end += length;
  }
  end = start > end ? 0 : toLength(end);
  while (start < end) {
    array2[start++] = value;
  }
  return array2;
}
function fill(array2, value, start, end) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return [];
  }
  if (start && typeof start != "number" && isIterateeCall(array2, value, start)) {
    start = 0;
    end = length;
  }
  return baseFill(array2, value, start, end);
}
function baseFilter(collection2, predicate) {
  var result2 = [];
  baseEach(collection2, function(value, index, collection3) {
    if (predicate(value, index, collection3)) {
      result2.push(value);
    }
  });
  return result2;
}
function filter(collection2, predicate) {
  var func2 = isArray$2(collection2) ? arrayFilter : baseFilter;
  return func2(collection2, baseIteratee(predicate));
}
function createFind(findIndexFunc) {
  return function(collection2, predicate, fromIndex) {
    var iterable = Object(collection2);
    if (!isArrayLike(collection2)) {
      var iteratee2 = baseIteratee(predicate);
      collection2 = keys(collection2);
      predicate = function(key) {
        return iteratee2(iterable[key], key, iterable);
      };
    }
    var index = findIndexFunc(collection2, predicate, fromIndex);
    return index > -1 ? iterable[iteratee2 ? collection2[index] : index] : void 0;
  };
}
var nativeMax$6 = Math.max;
function findIndex(array2, predicate, fromIndex) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return -1;
  }
  var index = fromIndex == null ? 0 : toInteger(fromIndex);
  if (index < 0) {
    index = nativeMax$6(length + index, 0);
  }
  return baseFindIndex(array2, baseIteratee(predicate), index);
}
var find = createFind(findIndex);
function baseFindKey(collection2, predicate, eachFunc) {
  var result2;
  eachFunc(collection2, function(value, key, collection3) {
    if (predicate(value, key, collection3)) {
      result2 = key;
      return false;
    }
  });
  return result2;
}
function findKey$1(object2, predicate) {
  return baseFindKey(object2, baseIteratee(predicate), baseForOwn);
}
var nativeMax$7 = Math.max, nativeMin$4 = Math.min;
function findLastIndex(array2, predicate, fromIndex) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return -1;
  }
  var index = length - 1;
  if (fromIndex !== void 0) {
    index = toInteger(fromIndex);
    index = fromIndex < 0 ? nativeMax$7(length + index, 0) : nativeMin$4(index, length - 1);
  }
  return baseFindIndex(array2, baseIteratee(predicate), index, true);
}
var findLast = createFind(findLastIndex);
function findLastKey(object2, predicate) {
  return baseFindKey(object2, baseIteratee(predicate), baseForOwnRight);
}
function head(array2) {
  return array2 && array2.length ? array2[0] : void 0;
}
function baseMap(collection2, iteratee2) {
  var index = -1, result2 = isArrayLike(collection2) ? Array(collection2.length) : [];
  baseEach(collection2, function(value, key, collection3) {
    result2[++index] = iteratee2(value, key, collection3);
  });
  return result2;
}
function map(collection2, iteratee2) {
  var func2 = isArray$2(collection2) ? arrayMap : baseMap;
  return func2(collection2, baseIteratee(iteratee2));
}
function flatMap(collection2, iteratee2) {
  return baseFlatten(map(collection2, iteratee2), 1);
}
var INFINITY$3 = 1 / 0;
function flatMapDeep(collection2, iteratee2) {
  return baseFlatten(map(collection2, iteratee2), INFINITY$3);
}
function flatMapDepth(collection2, iteratee2, depth) {
  depth = depth === void 0 ? 1 : toInteger(depth);
  return baseFlatten(map(collection2, iteratee2), depth);
}
var INFINITY$4 = 1 / 0;
function flattenDeep(array2) {
  var length = array2 == null ? 0 : array2.length;
  return length ? baseFlatten(array2, INFINITY$4) : [];
}
function flattenDepth(array2, depth) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return [];
  }
  depth = depth === void 0 ? 1 : toInteger(depth);
  return baseFlatten(array2, depth);
}
var WRAP_FLIP_FLAG$2 = 512;
function flip(func2) {
  return createWrap(func2, WRAP_FLIP_FLAG$2);
}
var floor = createRound("floor");
var FUNC_ERROR_TEXT$7 = "Expected a function";
var WRAP_CURRY_FLAG$6 = 8, WRAP_PARTIAL_FLAG$5 = 32, WRAP_ARY_FLAG$4 = 128, WRAP_REARG_FLAG$2 = 256;
function createFlow(fromRight) {
  return flatRest(function(funcs) {
    var length = funcs.length, index = length, prereq = LodashWrapper.prototype.thru;
    if (fromRight) {
      funcs.reverse();
    }
    while (index--) {
      var func2 = funcs[index];
      if (typeof func2 != "function") {
        throw new TypeError(FUNC_ERROR_TEXT$7);
      }
      if (prereq && !wrapper && getFuncName(func2) == "wrapper") {
        var wrapper = new LodashWrapper([], true);
      }
    }
    index = wrapper ? index : length;
    while (++index < length) {
      func2 = funcs[index];
      var funcName = getFuncName(func2), data = funcName == "wrapper" ? getData(func2) : void 0;
      if (data && isLaziable(data[0]) && data[1] == (WRAP_ARY_FLAG$4 | WRAP_CURRY_FLAG$6 | WRAP_PARTIAL_FLAG$5 | WRAP_REARG_FLAG$2) && !data[4].length && data[9] == 1) {
        wrapper = wrapper[getFuncName(data[0])].apply(wrapper, data[3]);
      } else {
        wrapper = func2.length == 1 && isLaziable(func2) ? wrapper[funcName]() : wrapper.thru(func2);
      }
    }
    return function() {
      var args = arguments, value = args[0];
      if (wrapper && args.length == 1 && isArray$2(value)) {
        return wrapper.plant(value).value();
      }
      var index2 = 0, result2 = length ? funcs[index2].apply(this, args) : value;
      while (++index2 < length) {
        result2 = funcs[index2].call(this, result2);
      }
      return result2;
    };
  });
}
var flow = createFlow();
var flowRight = createFlow(true);
function forIn(object2, iteratee2) {
  return object2 == null ? object2 : baseFor(object2, castFunction(iteratee2), keysIn);
}
function forInRight(object2, iteratee2) {
  return object2 == null ? object2 : baseForRight(object2, castFunction(iteratee2), keysIn);
}
function forOwn(object2, iteratee2) {
  return object2 && baseForOwn(object2, castFunction(iteratee2));
}
function forOwnRight(object2, iteratee2) {
  return object2 && baseForOwnRight(object2, castFunction(iteratee2));
}
function fromPairs(pairs) {
  var index = -1, length = pairs == null ? 0 : pairs.length, result2 = {};
  while (++index < length) {
    var pair = pairs[index];
    result2[pair[0]] = pair[1];
  }
  return result2;
}
function baseFunctions(object2, props) {
  return arrayFilter(props, function(key) {
    return isFunction$1(object2[key]);
  });
}
function functions(object2) {
  return object2 == null ? [] : baseFunctions(object2, keys(object2));
}
function functionsIn(object2) {
  return object2 == null ? [] : baseFunctions(object2, keysIn(object2));
}
var objectProto$l = Object.prototype;
var hasOwnProperty$i = objectProto$l.hasOwnProperty;
var groupBy = createAggregator(function(result2, value, key) {
  if (hasOwnProperty$i.call(result2, key)) {
    result2[key].push(value);
  } else {
    baseAssignValue(result2, key, [value]);
  }
});
function baseGt(value, other) {
  return value > other;
}
function createRelationalOperation(operator) {
  return function(value, other) {
    if (!(typeof value == "string" && typeof other == "string")) {
      value = toNumber(value);
      other = toNumber(other);
    }
    return operator(value, other);
  };
}
var gt = createRelationalOperation(baseGt);
var gte = createRelationalOperation(function(value, other) {
  return value >= other;
});
var objectProto$m = Object.prototype;
var hasOwnProperty$j = objectProto$m.hasOwnProperty;
function baseHas(object2, key) {
  return object2 != null && hasOwnProperty$j.call(object2, key);
}
function has(object2, path) {
  return object2 != null && hasPath(object2, path, baseHas);
}
var nativeMax$8 = Math.max, nativeMin$5 = Math.min;
function baseInRange(number2, start, end) {
  return number2 >= nativeMin$5(start, end) && number2 < nativeMax$8(start, end);
}
function inRange(number2, start, end) {
  start = toFinite(start);
  if (end === void 0) {
    end = start;
    start = 0;
  } else {
    end = toFinite(end);
  }
  number2 = toNumber(number2);
  return baseInRange(number2, start, end);
}
var stringTag$4 = "[object String]";
function isString$1(value) {
  return typeof value == "string" || !isArray$2(value) && isObjectLike(value) && baseGetTag(value) == stringTag$4;
}
function baseValues(object2, props) {
  return arrayMap(props, function(key) {
    return object2[key];
  });
}
function values(object2) {
  return object2 == null ? [] : baseValues(object2, keys(object2));
}
var nativeMax$9 = Math.max;
function includes(collection2, value, fromIndex, guard) {
  collection2 = isArrayLike(collection2) ? collection2 : values(collection2);
  fromIndex = fromIndex && !guard ? toInteger(fromIndex) : 0;
  var length = collection2.length;
  if (fromIndex < 0) {
    fromIndex = nativeMax$9(length + fromIndex, 0);
  }
  return isString$1(collection2) ? fromIndex <= length && collection2.indexOf(value, fromIndex) > -1 : !!length && baseIndexOf(collection2, value, fromIndex) > -1;
}
var nativeMax$a = Math.max;
function indexOf(array2, value, fromIndex) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return -1;
  }
  var index = fromIndex == null ? 0 : toInteger(fromIndex);
  if (index < 0) {
    index = nativeMax$a(length + index, 0);
  }
  return baseIndexOf(array2, value, index);
}
function initial(array2) {
  var length = array2 == null ? 0 : array2.length;
  return length ? baseSlice(array2, 0, -1) : [];
}
var nativeMin$6 = Math.min;
function baseIntersection(arrays, iteratee2, comparator) {
  var includes2 = comparator ? arrayIncludesWith : arrayIncludes, length = arrays[0].length, othLength = arrays.length, othIndex = othLength, caches = Array(othLength), maxLength = Infinity, result2 = [];
  while (othIndex--) {
    var array2 = arrays[othIndex];
    if (othIndex && iteratee2) {
      array2 = arrayMap(array2, baseUnary(iteratee2));
    }
    maxLength = nativeMin$6(array2.length, maxLength);
    caches[othIndex] = !comparator && (iteratee2 || length >= 120 && array2.length >= 120) ? new SetCache(othIndex && array2) : void 0;
  }
  array2 = arrays[0];
  var index = -1, seen = caches[0];
  outer:
    while (++index < length && result2.length < maxLength) {
      var value = array2[index], computed = iteratee2 ? iteratee2(value) : value;
      value = comparator || value !== 0 ? value : 0;
      if (!(seen ? cacheHas(seen, computed) : includes2(result2, computed, comparator))) {
        othIndex = othLength;
        while (--othIndex) {
          var cache = caches[othIndex];
          if (!(cache ? cacheHas(cache, computed) : includes2(arrays[othIndex], computed, comparator))) {
            continue outer;
          }
        }
        if (seen) {
          seen.push(computed);
        }
        result2.push(value);
      }
    }
  return result2;
}
function castArrayLikeObject(value) {
  return isArrayLikeObject(value) ? value : [];
}
var intersection = baseRest(function(arrays) {
  var mapped = arrayMap(arrays, castArrayLikeObject);
  return mapped.length && mapped[0] === arrays[0] ? baseIntersection(mapped) : [];
});
var intersectionBy = baseRest(function(arrays) {
  var iteratee2 = last(arrays), mapped = arrayMap(arrays, castArrayLikeObject);
  if (iteratee2 === last(mapped)) {
    iteratee2 = void 0;
  } else {
    mapped.pop();
  }
  return mapped.length && mapped[0] === arrays[0] ? baseIntersection(mapped, baseIteratee(iteratee2)) : [];
});
var intersectionWith = baseRest(function(arrays) {
  var comparator = last(arrays), mapped = arrayMap(arrays, castArrayLikeObject);
  comparator = typeof comparator == "function" ? comparator : void 0;
  if (comparator) {
    mapped.pop();
  }
  return mapped.length && mapped[0] === arrays[0] ? baseIntersection(mapped, void 0, comparator) : [];
});
function baseInverter(object2, setter, iteratee2, accumulator) {
  baseForOwn(object2, function(value, key, object3) {
    setter(accumulator, iteratee2(value), key, object3);
  });
  return accumulator;
}
function createInverter(setter, toIteratee) {
  return function(object2, iteratee2) {
    return baseInverter(object2, setter, toIteratee(iteratee2), {});
  };
}
var objectProto$n = Object.prototype;
var nativeObjectToString$2 = objectProto$n.toString;
var invert = createInverter(function(result2, value, key) {
  if (value != null && typeof value.toString != "function") {
    value = nativeObjectToString$2.call(value);
  }
  result2[value] = key;
}, constant(identity$1));
var objectProto$o = Object.prototype;
var hasOwnProperty$k = objectProto$o.hasOwnProperty;
var nativeObjectToString$3 = objectProto$o.toString;
var invertBy = createInverter(function(result2, value, key) {
  if (value != null && typeof value.toString != "function") {
    value = nativeObjectToString$3.call(value);
  }
  if (hasOwnProperty$k.call(result2, value)) {
    result2[value].push(key);
  } else {
    result2[value] = [key];
  }
}, baseIteratee);
function parent(object2, path) {
  return path.length < 2 ? object2 : baseGet(object2, baseSlice(path, 0, -1));
}
function baseInvoke(object2, path, args) {
  path = castPath(path, object2);
  object2 = parent(object2, path);
  var func2 = object2 == null ? object2 : object2[toKey(last(path))];
  return func2 == null ? void 0 : apply(func2, object2, args);
}
var invoke = baseRest(baseInvoke);
var invokeMap = baseRest(function(collection2, path, args) {
  var index = -1, isFunc = typeof path == "function", result2 = isArrayLike(collection2) ? Array(collection2.length) : [];
  baseEach(collection2, function(value) {
    result2[++index] = isFunc ? apply(path, value, args) : baseInvoke(value, path, args);
  });
  return result2;
});
var arrayBufferTag$4 = "[object ArrayBuffer]";
function baseIsArrayBuffer(value) {
  return isObjectLike(value) && baseGetTag(value) == arrayBufferTag$4;
}
var nodeIsArrayBuffer = nodeUtil && nodeUtil.isArrayBuffer;
var isArrayBuffer$1 = nodeIsArrayBuffer ? baseUnary(nodeIsArrayBuffer) : baseIsArrayBuffer;
var boolTag$4 = "[object Boolean]";
function isBoolean$1(value) {
  return value === true || value === false || isObjectLike(value) && baseGetTag(value) == boolTag$4;
}
var dateTag$4 = "[object Date]";
function baseIsDate(value) {
  return isObjectLike(value) && baseGetTag(value) == dateTag$4;
}
var nodeIsDate = nodeUtil && nodeUtil.isDate;
var isDate$1 = nodeIsDate ? baseUnary(nodeIsDate) : baseIsDate;
function isElement(value) {
  return isObjectLike(value) && value.nodeType === 1 && !isPlainObject$1(value);
}
var mapTag$7 = "[object Map]", setTag$7 = "[object Set]";
var objectProto$p = Object.prototype;
var hasOwnProperty$l = objectProto$p.hasOwnProperty;
function isEmpty(value) {
  if (value == null) {
    return true;
  }
  if (isArrayLike(value) && (isArray$2(value) || typeof value == "string" || typeof value.splice == "function" || isBuffer$2(value) || isTypedArray$1(value) || isArguments(value))) {
    return !value.length;
  }
  var tag = getTag$1(value);
  if (tag == mapTag$7 || tag == setTag$7) {
    return !value.size;
  }
  if (isPrototype(value)) {
    return !baseKeys(value).length;
  }
  for (var key in value) {
    if (hasOwnProperty$l.call(value, key)) {
      return false;
    }
  }
  return true;
}
function isEqual(value, other) {
  return baseIsEqual(value, other);
}
function isEqualWith(value, other, customizer) {
  customizer = typeof customizer == "function" ? customizer : void 0;
  var result2 = customizer ? customizer(value, other) : void 0;
  return result2 === void 0 ? baseIsEqual(value, other, void 0, customizer) : !!result2;
}
var nativeIsFinite$1 = root.isFinite;
function isFinite$1(value) {
  return typeof value == "number" && nativeIsFinite$1(value);
}
function isInteger(value) {
  return typeof value == "number" && value == toInteger(value);
}
function isMatch(object2, source) {
  return object2 === source || baseIsMatch(object2, source, getMatchData(source));
}
function isMatchWith(object2, source, customizer) {
  customizer = typeof customizer == "function" ? customizer : void 0;
  return baseIsMatch(object2, source, getMatchData(source), customizer);
}
var numberTag$4 = "[object Number]";
function isNumber$1(value) {
  return typeof value == "number" || isObjectLike(value) && baseGetTag(value) == numberTag$4;
}
function isNaN$1(value) {
  return isNumber$1(value) && value != +value;
}
var isMaskable = coreJsData ? isFunction$1 : stubFalse;
var CORE_ERROR_TEXT = "Unsupported core-js use. Try https://npms.io/search?q=ponyfill.";
function isNative(value) {
  if (isMaskable(value)) {
    throw new Error(CORE_ERROR_TEXT);
  }
  return baseIsNative(value);
}
function isNil(value) {
  return value == null;
}
function isNull(value) {
  return value === null;
}
var regexpTag$4 = "[object RegExp]";
function baseIsRegExp(value) {
  return isObjectLike(value) && baseGetTag(value) == regexpTag$4;
}
var nodeIsRegExp = nodeUtil && nodeUtil.isRegExp;
var isRegExp$1 = nodeIsRegExp ? baseUnary(nodeIsRegExp) : baseIsRegExp;
var MAX_SAFE_INTEGER$2 = 9007199254740991;
function isSafeInteger(value) {
  return isInteger(value) && value >= -MAX_SAFE_INTEGER$2 && value <= MAX_SAFE_INTEGER$2;
}
function isUndefined$1(value) {
  return value === void 0;
}
var weakMapTag$3 = "[object WeakMap]";
function isWeakMap(value) {
  return isObjectLike(value) && getTag$1(value) == weakMapTag$3;
}
var weakSetTag = "[object WeakSet]";
function isWeakSet(value) {
  return isObjectLike(value) && baseGetTag(value) == weakSetTag;
}
var CLONE_DEEP_FLAG$4 = 1;
function iteratee(func2) {
  return baseIteratee(typeof func2 == "function" ? func2 : baseClone(func2, CLONE_DEEP_FLAG$4));
}
var arrayProto$1 = Array.prototype;
var nativeJoin = arrayProto$1.join;
function join(array2, separator) {
  return array2 == null ? "" : nativeJoin.call(array2, separator);
}
var kebabCase = createCompounder(function(result2, word, index) {
  return result2 + (index ? "-" : "") + word.toLowerCase();
});
var keyBy = createAggregator(function(result2, value, key) {
  baseAssignValue(result2, key, value);
});
function strictLastIndexOf(array2, value, fromIndex) {
  var index = fromIndex + 1;
  while (index--) {
    if (array2[index] === value) {
      return index;
    }
  }
  return index;
}
var nativeMax$b = Math.max, nativeMin$7 = Math.min;
function lastIndexOf(array2, value, fromIndex) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return -1;
  }
  var index = length;
  if (fromIndex !== void 0) {
    index = toInteger(fromIndex);
    index = index < 0 ? nativeMax$b(length + index, 0) : nativeMin$7(index, length - 1);
  }
  return value === value ? strictLastIndexOf(array2, value, index) : baseFindIndex(array2, baseIsNaN, index, true);
}
var lowerCase = createCompounder(function(result2, word, index) {
  return result2 + (index ? " " : "") + word.toLowerCase();
});
var lowerFirst = createCaseFirst("toLowerCase");
function baseLt(value, other) {
  return value < other;
}
var lt = createRelationalOperation(baseLt);
var lte = createRelationalOperation(function(value, other) {
  return value <= other;
});
function mapKeys(object2, iteratee2) {
  var result2 = {};
  iteratee2 = baseIteratee(iteratee2);
  baseForOwn(object2, function(value, key, object3) {
    baseAssignValue(result2, iteratee2(value, key, object3), value);
  });
  return result2;
}
function mapValues(object2, iteratee2) {
  var result2 = {};
  iteratee2 = baseIteratee(iteratee2);
  baseForOwn(object2, function(value, key, object3) {
    baseAssignValue(result2, key, iteratee2(value, key, object3));
  });
  return result2;
}
var CLONE_DEEP_FLAG$5 = 1;
function matches(source) {
  return baseMatches(baseClone(source, CLONE_DEEP_FLAG$5));
}
var CLONE_DEEP_FLAG$6 = 1;
function matchesProperty(path, srcValue) {
  return baseMatchesProperty(path, baseClone(srcValue, CLONE_DEEP_FLAG$6));
}
function baseExtremum(array2, iteratee2, comparator) {
  var index = -1, length = array2.length;
  while (++index < length) {
    var value = array2[index], current = iteratee2(value);
    if (current != null && (computed === void 0 ? current === current && !isSymbol(current) : comparator(current, computed))) {
      var computed = current, result2 = value;
    }
  }
  return result2;
}
function max(array2) {
  return array2 && array2.length ? baseExtremum(array2, identity$1, baseGt) : void 0;
}
function maxBy(array2, iteratee2) {
  return array2 && array2.length ? baseExtremum(array2, baseIteratee(iteratee2), baseGt) : void 0;
}
function baseSum(array2, iteratee2) {
  var result2, index = -1, length = array2.length;
  while (++index < length) {
    var current = iteratee2(array2[index]);
    if (current !== void 0) {
      result2 = result2 === void 0 ? current : result2 + current;
    }
  }
  return result2;
}
var NAN$2 = 0 / 0;
function baseMean(array2, iteratee2) {
  var length = array2 == null ? 0 : array2.length;
  return length ? baseSum(array2, iteratee2) / length : NAN$2;
}
function mean(array2) {
  return baseMean(array2, identity$1);
}
function meanBy(array2, iteratee2) {
  return baseMean(array2, baseIteratee(iteratee2));
}
var merge$1 = createAssigner(function(object2, source, srcIndex) {
  baseMerge(object2, source, srcIndex);
});
var method = baseRest(function(path, args) {
  return function(object2) {
    return baseInvoke(object2, path, args);
  };
});
var methodOf = baseRest(function(object2, args) {
  return function(path) {
    return baseInvoke(object2, path, args);
  };
});
function min(array2) {
  return array2 && array2.length ? baseExtremum(array2, identity$1, baseLt) : void 0;
}
function minBy(array2, iteratee2) {
  return array2 && array2.length ? baseExtremum(array2, baseIteratee(iteratee2), baseLt) : void 0;
}
function mixin(object2, source, options) {
  var props = keys(source), methodNames = baseFunctions(source, props);
  var chain2 = !(isObject$1(options) && "chain" in options) || !!options.chain, isFunc = isFunction$1(object2);
  arrayEach(methodNames, function(methodName) {
    var func2 = source[methodName];
    object2[methodName] = func2;
    if (isFunc) {
      object2.prototype[methodName] = function() {
        var chainAll = this.__chain__;
        if (chain2 || chainAll) {
          var result2 = object2(this.__wrapped__), actions = result2.__actions__ = copyArray(this.__actions__);
          actions.push({func: func2, args: arguments, thisArg: object2});
          result2.__chain__ = chainAll;
          return result2;
        }
        return func2.apply(object2, arrayPush([this.value()], arguments));
      };
    }
  });
  return object2;
}
var multiply = createMathOperation(function(multiplier, multiplicand) {
  return multiplier * multiplicand;
}, 1);
var FUNC_ERROR_TEXT$8 = "Expected a function";
function negate(predicate) {
  if (typeof predicate != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$8);
  }
  return function() {
    var args = arguments;
    switch (args.length) {
      case 0:
        return !predicate.call(this);
      case 1:
        return !predicate.call(this, args[0]);
      case 2:
        return !predicate.call(this, args[0], args[1]);
      case 3:
        return !predicate.call(this, args[0], args[1], args[2]);
    }
    return !predicate.apply(this, args);
  };
}
function iteratorToArray(iterator) {
  var data, result2 = [];
  while (!(data = iterator.next()).done) {
    result2.push(data.value);
  }
  return result2;
}
var mapTag$8 = "[object Map]", setTag$8 = "[object Set]";
var symIterator = Symbol$1 ? Symbol$1.iterator : void 0;
function toArray$1(value) {
  if (!value) {
    return [];
  }
  if (isArrayLike(value)) {
    return isString$1(value) ? stringToArray(value) : copyArray(value);
  }
  if (symIterator && value[symIterator]) {
    return iteratorToArray(value[symIterator]());
  }
  var tag = getTag$1(value), func2 = tag == mapTag$8 ? mapToArray : tag == setTag$8 ? setToArray : values;
  return func2(value);
}
function wrapperNext() {
  if (this.__values__ === void 0) {
    this.__values__ = toArray$1(this.value());
  }
  var done = this.__index__ >= this.__values__.length, value = done ? void 0 : this.__values__[this.__index__++];
  return {done, value};
}
function baseNth(array2, n) {
  var length = array2.length;
  if (!length) {
    return;
  }
  n += n < 0 ? length : 0;
  return isIndex(n, length) ? array2[n] : void 0;
}
function nth(array2, n) {
  return array2 && array2.length ? baseNth(array2, toInteger(n)) : void 0;
}
function nthArg(n) {
  n = toInteger(n);
  return baseRest(function(args) {
    return baseNth(args, n);
  });
}
function baseUnset(object2, path) {
  path = castPath(path, object2);
  object2 = parent(object2, path);
  return object2 == null || delete object2[toKey(last(path))];
}
function customOmitClone(value) {
  return isPlainObject$1(value) ? void 0 : value;
}
var CLONE_DEEP_FLAG$7 = 1, CLONE_FLAT_FLAG$1 = 2, CLONE_SYMBOLS_FLAG$5 = 4;
var omit = flatRest(function(object2, paths) {
  var result2 = {};
  if (object2 == null) {
    return result2;
  }
  var isDeep = false;
  paths = arrayMap(paths, function(path) {
    path = castPath(path, object2);
    isDeep || (isDeep = path.length > 1);
    return path;
  });
  copyObject(object2, getAllKeysIn(object2), result2);
  if (isDeep) {
    result2 = baseClone(result2, CLONE_DEEP_FLAG$7 | CLONE_FLAT_FLAG$1 | CLONE_SYMBOLS_FLAG$5, customOmitClone);
  }
  var length = paths.length;
  while (length--) {
    baseUnset(result2, paths[length]);
  }
  return result2;
});
function baseSet(object2, path, value, customizer) {
  if (!isObject$1(object2)) {
    return object2;
  }
  path = castPath(path, object2);
  var index = -1, length = path.length, lastIndex = length - 1, nested = object2;
  while (nested != null && ++index < length) {
    var key = toKey(path[index]), newValue = value;
    if (key === "__proto__" || key === "constructor" || key === "prototype") {
      return object2;
    }
    if (index != lastIndex) {
      var objValue = nested[key];
      newValue = customizer ? customizer(objValue, key, nested) : void 0;
      if (newValue === void 0) {
        newValue = isObject$1(objValue) ? objValue : isIndex(path[index + 1]) ? [] : {};
      }
    }
    assignValue(nested, key, newValue);
    nested = nested[key];
  }
  return object2;
}
function basePickBy(object2, paths, predicate) {
  var index = -1, length = paths.length, result2 = {};
  while (++index < length) {
    var path = paths[index], value = baseGet(object2, path);
    if (predicate(value, path)) {
      baseSet(result2, castPath(path, object2), value);
    }
  }
  return result2;
}
function pickBy(object2, predicate) {
  if (object2 == null) {
    return {};
  }
  var props = arrayMap(getAllKeysIn(object2), function(prop) {
    return [prop];
  });
  predicate = baseIteratee(predicate);
  return basePickBy(object2, props, function(value, path) {
    return predicate(value, path[0]);
  });
}
function omitBy(object2, predicate) {
  return pickBy(object2, negate(baseIteratee(predicate)));
}
function once(func2) {
  return before(2, func2);
}
function baseSortBy(array2, comparer) {
  var length = array2.length;
  array2.sort(comparer);
  while (length--) {
    array2[length] = array2[length].value;
  }
  return array2;
}
function compareAscending(value, other) {
  if (value !== other) {
    var valIsDefined = value !== void 0, valIsNull = value === null, valIsReflexive = value === value, valIsSymbol = isSymbol(value);
    var othIsDefined = other !== void 0, othIsNull = other === null, othIsReflexive = other === other, othIsSymbol = isSymbol(other);
    if (!othIsNull && !othIsSymbol && !valIsSymbol && value > other || valIsSymbol && othIsDefined && othIsReflexive && !othIsNull && !othIsSymbol || valIsNull && othIsDefined && othIsReflexive || !valIsDefined && othIsReflexive || !valIsReflexive) {
      return 1;
    }
    if (!valIsNull && !valIsSymbol && !othIsSymbol && value < other || othIsSymbol && valIsDefined && valIsReflexive && !valIsNull && !valIsSymbol || othIsNull && valIsDefined && valIsReflexive || !othIsDefined && valIsReflexive || !othIsReflexive) {
      return -1;
    }
  }
  return 0;
}
function compareMultiple(object2, other, orders) {
  var index = -1, objCriteria = object2.criteria, othCriteria = other.criteria, length = objCriteria.length, ordersLength = orders.length;
  while (++index < length) {
    var result2 = compareAscending(objCriteria[index], othCriteria[index]);
    if (result2) {
      if (index >= ordersLength) {
        return result2;
      }
      var order = orders[index];
      return result2 * (order == "desc" ? -1 : 1);
    }
  }
  return object2.index - other.index;
}
function baseOrderBy(collection2, iteratees, orders) {
  if (iteratees.length) {
    iteratees = arrayMap(iteratees, function(iteratee2) {
      if (isArray$2(iteratee2)) {
        return function(value) {
          return baseGet(value, iteratee2.length === 1 ? iteratee2[0] : iteratee2);
        };
      }
      return iteratee2;
    });
  } else {
    iteratees = [identity$1];
  }
  var index = -1;
  iteratees = arrayMap(iteratees, baseUnary(baseIteratee));
  var result2 = baseMap(collection2, function(value, key, collection3) {
    var criteria = arrayMap(iteratees, function(iteratee2) {
      return iteratee2(value);
    });
    return {criteria, index: ++index, value};
  });
  return baseSortBy(result2, function(object2, other) {
    return compareMultiple(object2, other, orders);
  });
}
function orderBy(collection2, iteratees, orders, guard) {
  if (collection2 == null) {
    return [];
  }
  if (!isArray$2(iteratees)) {
    iteratees = iteratees == null ? [] : [iteratees];
  }
  orders = guard ? void 0 : orders;
  if (!isArray$2(orders)) {
    orders = orders == null ? [] : [orders];
  }
  return baseOrderBy(collection2, iteratees, orders);
}
function createOver(arrayFunc) {
  return flatRest(function(iteratees) {
    iteratees = arrayMap(iteratees, baseUnary(baseIteratee));
    return baseRest(function(args) {
      var thisArg = this;
      return arrayFunc(iteratees, function(iteratee2) {
        return apply(iteratee2, thisArg, args);
      });
    });
  });
}
var over = createOver(arrayMap);
var castRest = baseRest;
var nativeMin$8 = Math.min;
var overArgs = castRest(function(func2, transforms) {
  transforms = transforms.length == 1 && isArray$2(transforms[0]) ? arrayMap(transforms[0], baseUnary(baseIteratee)) : arrayMap(baseFlatten(transforms, 1), baseUnary(baseIteratee));
  var funcsLength = transforms.length;
  return baseRest(function(args) {
    var index = -1, length = nativeMin$8(args.length, funcsLength);
    while (++index < length) {
      args[index] = transforms[index].call(this, args[index]);
    }
    return apply(func2, this, args);
  });
});
var overEvery = createOver(arrayEvery);
var overSome = createOver(arraySome);
var MAX_SAFE_INTEGER$3 = 9007199254740991;
var nativeFloor = Math.floor;
function baseRepeat(string2, n) {
  var result2 = "";
  if (!string2 || n < 1 || n > MAX_SAFE_INTEGER$3) {
    return result2;
  }
  do {
    if (n % 2) {
      result2 += string2;
    }
    n = nativeFloor(n / 2);
    if (n) {
      string2 += string2;
    }
  } while (n);
  return result2;
}
var asciiSize = baseProperty("length");
var rsAstralRange$3 = "\\ud800-\\udfff", rsComboMarksRange$4 = "\\u0300-\\u036f", reComboHalfMarksRange$4 = "\\ufe20-\\ufe2f", rsComboSymbolsRange$4 = "\\u20d0-\\u20ff", rsComboRange$4 = rsComboMarksRange$4 + reComboHalfMarksRange$4 + rsComboSymbolsRange$4, rsVarRange$3 = "\\ufe0e\\ufe0f";
var rsAstral$1 = "[" + rsAstralRange$3 + "]", rsCombo$3 = "[" + rsComboRange$4 + "]", rsFitz$2 = "\\ud83c[\\udffb-\\udfff]", rsModifier$2 = "(?:" + rsCombo$3 + "|" + rsFitz$2 + ")", rsNonAstral$2 = "[^" + rsAstralRange$3 + "]", rsRegional$2 = "(?:\\ud83c[\\udde6-\\uddff]){2}", rsSurrPair$2 = "[\\ud800-\\udbff][\\udc00-\\udfff]", rsZWJ$3 = "\\u200d";
var reOptMod$2 = rsModifier$2 + "?", rsOptVar$2 = "[" + rsVarRange$3 + "]?", rsOptJoin$2 = "(?:" + rsZWJ$3 + "(?:" + [rsNonAstral$2, rsRegional$2, rsSurrPair$2].join("|") + ")" + rsOptVar$2 + reOptMod$2 + ")*", rsSeq$2 = rsOptVar$2 + reOptMod$2 + rsOptJoin$2, rsSymbol$1 = "(?:" + [rsNonAstral$2 + rsCombo$3 + "?", rsCombo$3, rsRegional$2, rsSurrPair$2, rsAstral$1].join("|") + ")";
var reUnicode$1 = RegExp(rsFitz$2 + "(?=" + rsFitz$2 + ")|" + rsSymbol$1 + rsSeq$2, "g");
function unicodeSize(string2) {
  var result2 = reUnicode$1.lastIndex = 0;
  while (reUnicode$1.test(string2)) {
    ++result2;
  }
  return result2;
}
function stringSize(string2) {
  return hasUnicode(string2) ? unicodeSize(string2) : asciiSize(string2);
}
var nativeCeil$1 = Math.ceil;
function createPadding(length, chars) {
  chars = chars === void 0 ? " " : baseToString(chars);
  var charsLength = chars.length;
  if (charsLength < 2) {
    return charsLength ? baseRepeat(chars, length) : chars;
  }
  var result2 = baseRepeat(chars, nativeCeil$1(length / stringSize(chars)));
  return hasUnicode(chars) ? castSlice(stringToArray(result2), 0, length).join("") : result2.slice(0, length);
}
var nativeCeil$2 = Math.ceil, nativeFloor$1 = Math.floor;
function pad(string2, length, chars) {
  string2 = toString$2(string2);
  length = toInteger(length);
  var strLength = length ? stringSize(string2) : 0;
  if (!length || strLength >= length) {
    return string2;
  }
  var mid = (length - strLength) / 2;
  return createPadding(nativeFloor$1(mid), chars) + string2 + createPadding(nativeCeil$2(mid), chars);
}
function padEnd(string2, length, chars) {
  string2 = toString$2(string2);
  length = toInteger(length);
  var strLength = length ? stringSize(string2) : 0;
  return length && strLength < length ? string2 + createPadding(length - strLength, chars) : string2;
}
function padStart(string2, length, chars) {
  string2 = toString$2(string2);
  length = toInteger(length);
  var strLength = length ? stringSize(string2) : 0;
  return length && strLength < length ? createPadding(length - strLength, chars) + string2 : string2;
}
var reTrimStart$1 = /^\s+/;
var nativeParseInt = root.parseInt;
function parseInt$1(string2, radix, guard) {
  if (guard || radix == null) {
    radix = 0;
  } else if (radix) {
    radix = +radix;
  }
  return nativeParseInt(toString$2(string2).replace(reTrimStart$1, ""), radix || 0);
}
var WRAP_PARTIAL_FLAG$6 = 32;
var partial = baseRest(function(func2, partials) {
  var holders = replaceHolders(partials, getHolder(partial));
  return createWrap(func2, WRAP_PARTIAL_FLAG$6, void 0, partials, holders);
});
partial.placeholder = {};
var WRAP_PARTIAL_RIGHT_FLAG$3 = 64;
var partialRight = baseRest(function(func2, partials) {
  var holders = replaceHolders(partials, getHolder(partialRight));
  return createWrap(func2, WRAP_PARTIAL_RIGHT_FLAG$3, void 0, partials, holders);
});
partialRight.placeholder = {};
var partition = createAggregator(function(result2, value, key) {
  result2[key ? 0 : 1].push(value);
}, function() {
  return [[], []];
});
function basePick(object2, paths) {
  return basePickBy(object2, paths, function(value, path) {
    return hasIn(object2, path);
  });
}
var pick = flatRest(function(object2, paths) {
  return object2 == null ? {} : basePick(object2, paths);
});
function wrapperPlant(value) {
  var result2, parent2 = this;
  while (parent2 instanceof baseLodash) {
    var clone2 = wrapperClone(parent2);
    clone2.__index__ = 0;
    clone2.__values__ = void 0;
    if (result2) {
      previous.__wrapped__ = clone2;
    } else {
      result2 = clone2;
    }
    var previous = clone2;
    parent2 = parent2.__wrapped__;
  }
  previous.__wrapped__ = value;
  return result2;
}
function propertyOf(object2) {
  return function(path) {
    return object2 == null ? void 0 : baseGet(object2, path);
  };
}
function baseIndexOfWith(array2, value, fromIndex, comparator) {
  var index = fromIndex - 1, length = array2.length;
  while (++index < length) {
    if (comparator(array2[index], value)) {
      return index;
    }
  }
  return -1;
}
var arrayProto$2 = Array.prototype;
var splice$1 = arrayProto$2.splice;
function basePullAll(array2, values2, iteratee2, comparator) {
  var indexOf2 = comparator ? baseIndexOfWith : baseIndexOf, index = -1, length = values2.length, seen = array2;
  if (array2 === values2) {
    values2 = copyArray(values2);
  }
  if (iteratee2) {
    seen = arrayMap(array2, baseUnary(iteratee2));
  }
  while (++index < length) {
    var fromIndex = 0, value = values2[index], computed = iteratee2 ? iteratee2(value) : value;
    while ((fromIndex = indexOf2(seen, computed, fromIndex, comparator)) > -1) {
      if (seen !== array2) {
        splice$1.call(seen, fromIndex, 1);
      }
      splice$1.call(array2, fromIndex, 1);
    }
  }
  return array2;
}
function pullAll(array2, values2) {
  return array2 && array2.length && values2 && values2.length ? basePullAll(array2, values2) : array2;
}
var pull = baseRest(pullAll);
function pullAllBy(array2, values2, iteratee2) {
  return array2 && array2.length && values2 && values2.length ? basePullAll(array2, values2, baseIteratee(iteratee2)) : array2;
}
function pullAllWith(array2, values2, comparator) {
  return array2 && array2.length && values2 && values2.length ? basePullAll(array2, values2, void 0, comparator) : array2;
}
var arrayProto$3 = Array.prototype;
var splice$2 = arrayProto$3.splice;
function basePullAt(array2, indexes) {
  var length = array2 ? indexes.length : 0, lastIndex = length - 1;
  while (length--) {
    var index = indexes[length];
    if (length == lastIndex || index !== previous) {
      var previous = index;
      if (isIndex(index)) {
        splice$2.call(array2, index, 1);
      } else {
        baseUnset(array2, index);
      }
    }
  }
  return array2;
}
var pullAt = flatRest(function(array2, indexes) {
  var length = array2 == null ? 0 : array2.length, result2 = baseAt(array2, indexes);
  basePullAt(array2, arrayMap(indexes, function(index) {
    return isIndex(index, length) ? +index : index;
  }).sort(compareAscending));
  return result2;
});
var nativeFloor$2 = Math.floor, nativeRandom = Math.random;
function baseRandom(lower, upper) {
  return lower + nativeFloor$2(nativeRandom() * (upper - lower + 1));
}
var freeParseFloat = parseFloat;
var nativeMin$9 = Math.min, nativeRandom$1 = Math.random;
function random(lower, upper, floating) {
  if (floating && typeof floating != "boolean" && isIterateeCall(lower, upper, floating)) {
    upper = floating = void 0;
  }
  if (floating === void 0) {
    if (typeof upper == "boolean") {
      floating = upper;
      upper = void 0;
    } else if (typeof lower == "boolean") {
      floating = lower;
      lower = void 0;
    }
  }
  if (lower === void 0 && upper === void 0) {
    lower = 0;
    upper = 1;
  } else {
    lower = toFinite(lower);
    if (upper === void 0) {
      upper = lower;
      lower = 0;
    } else {
      upper = toFinite(upper);
    }
  }
  if (lower > upper) {
    var temp = lower;
    lower = upper;
    upper = temp;
  }
  if (floating || lower % 1 || upper % 1) {
    var rand = nativeRandom$1();
    return nativeMin$9(lower + rand * (upper - lower + freeParseFloat("1e-" + ((rand + "").length - 1))), upper);
  }
  return baseRandom(lower, upper);
}
var nativeCeil$3 = Math.ceil, nativeMax$c = Math.max;
function baseRange(start, end, step, fromRight) {
  var index = -1, length = nativeMax$c(nativeCeil$3((end - start) / (step || 1)), 0), result2 = Array(length);
  while (length--) {
    result2[fromRight ? length : ++index] = start;
    start += step;
  }
  return result2;
}
function createRange(fromRight) {
  return function(start, end, step) {
    if (step && typeof step != "number" && isIterateeCall(start, end, step)) {
      end = step = void 0;
    }
    start = toFinite(start);
    if (end === void 0) {
      end = start;
      start = 0;
    } else {
      end = toFinite(end);
    }
    step = step === void 0 ? start < end ? 1 : -1 : toFinite(step);
    return baseRange(start, end, step, fromRight);
  };
}
var range = createRange();
var rangeRight = createRange(true);
var WRAP_REARG_FLAG$3 = 256;
var rearg = flatRest(function(func2, indexes) {
  return createWrap(func2, WRAP_REARG_FLAG$3, void 0, void 0, void 0, indexes);
});
function baseReduce(collection2, iteratee2, accumulator, initAccum, eachFunc) {
  eachFunc(collection2, function(value, index, collection3) {
    accumulator = initAccum ? (initAccum = false, value) : iteratee2(accumulator, value, index, collection3);
  });
  return accumulator;
}
function reduce(collection2, iteratee2, accumulator) {
  var func2 = isArray$2(collection2) ? arrayReduce : baseReduce, initAccum = arguments.length < 3;
  return func2(collection2, baseIteratee(iteratee2), accumulator, initAccum, baseEach);
}
function arrayReduceRight(array2, iteratee2, accumulator, initAccum) {
  var length = array2 == null ? 0 : array2.length;
  if (initAccum && length) {
    accumulator = array2[--length];
  }
  while (length--) {
    accumulator = iteratee2(accumulator, array2[length], length, array2);
  }
  return accumulator;
}
function reduceRight(collection2, iteratee2, accumulator) {
  var func2 = isArray$2(collection2) ? arrayReduceRight : baseReduce, initAccum = arguments.length < 3;
  return func2(collection2, baseIteratee(iteratee2), accumulator, initAccum, baseEachRight);
}
function reject(collection2, predicate) {
  var func2 = isArray$2(collection2) ? arrayFilter : baseFilter;
  return func2(collection2, negate(baseIteratee(predicate)));
}
function remove(array2, predicate) {
  var result2 = [];
  if (!(array2 && array2.length)) {
    return result2;
  }
  var index = -1, indexes = [], length = array2.length;
  predicate = baseIteratee(predicate);
  while (++index < length) {
    var value = array2[index];
    if (predicate(value, index, array2)) {
      result2.push(value);
      indexes.push(index);
    }
  }
  basePullAt(array2, indexes);
  return result2;
}
function repeat(string2, n, guard) {
  if (guard ? isIterateeCall(string2, n, guard) : n === void 0) {
    n = 1;
  } else {
    n = toInteger(n);
  }
  return baseRepeat(toString$2(string2), n);
}
function replace() {
  var args = arguments, string2 = toString$2(args[0]);
  return args.length < 3 ? string2 : string2.replace(args[1], args[2]);
}
var FUNC_ERROR_TEXT$9 = "Expected a function";
function rest(func2, start) {
  if (typeof func2 != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$9);
  }
  start = start === void 0 ? start : toInteger(start);
  return baseRest(func2, start);
}
function result(object2, path, defaultValue) {
  path = castPath(path, object2);
  var index = -1, length = path.length;
  if (!length) {
    length = 1;
    object2 = void 0;
  }
  while (++index < length) {
    var value = object2 == null ? void 0 : object2[toKey(path[index])];
    if (value === void 0) {
      index = length;
      value = defaultValue;
    }
    object2 = isFunction$1(value) ? value.call(object2) : value;
  }
  return object2;
}
var arrayProto$4 = Array.prototype;
var nativeReverse = arrayProto$4.reverse;
function reverse(array2) {
  return array2 == null ? array2 : nativeReverse.call(array2);
}
var round = createRound("round");
function arraySample(array2) {
  var length = array2.length;
  return length ? array2[baseRandom(0, length - 1)] : void 0;
}
function baseSample(collection2) {
  return arraySample(values(collection2));
}
function sample(collection2) {
  var func2 = isArray$2(collection2) ? arraySample : baseSample;
  return func2(collection2);
}
function shuffleSelf(array2, size2) {
  var index = -1, length = array2.length, lastIndex = length - 1;
  size2 = size2 === void 0 ? length : size2;
  while (++index < size2) {
    var rand = baseRandom(index, lastIndex), value = array2[rand];
    array2[rand] = array2[index];
    array2[index] = value;
  }
  array2.length = size2;
  return array2;
}
function arraySampleSize(array2, n) {
  return shuffleSelf(copyArray(array2), baseClamp(n, 0, array2.length));
}
function baseSampleSize(collection2, n) {
  var array2 = values(collection2);
  return shuffleSelf(array2, baseClamp(n, 0, array2.length));
}
function sampleSize(collection2, n, guard) {
  if (guard ? isIterateeCall(collection2, n, guard) : n === void 0) {
    n = 1;
  } else {
    n = toInteger(n);
  }
  var func2 = isArray$2(collection2) ? arraySampleSize : baseSampleSize;
  return func2(collection2, n);
}
function set(object2, path, value) {
  return object2 == null ? object2 : baseSet(object2, path, value);
}
function setWith(object2, path, value, customizer) {
  customizer = typeof customizer == "function" ? customizer : void 0;
  return object2 == null ? object2 : baseSet(object2, path, value, customizer);
}
function arrayShuffle(array2) {
  return shuffleSelf(copyArray(array2));
}
function baseShuffle(collection2) {
  return shuffleSelf(values(collection2));
}
function shuffle(collection2) {
  var func2 = isArray$2(collection2) ? arrayShuffle : baseShuffle;
  return func2(collection2);
}
var mapTag$9 = "[object Map]", setTag$9 = "[object Set]";
function size(collection2) {
  if (collection2 == null) {
    return 0;
  }
  if (isArrayLike(collection2)) {
    return isString$1(collection2) ? stringSize(collection2) : collection2.length;
  }
  var tag = getTag$1(collection2);
  if (tag == mapTag$9 || tag == setTag$9) {
    return collection2.size;
  }
  return baseKeys(collection2).length;
}
function slice(array2, start, end) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return [];
  }
  if (end && typeof end != "number" && isIterateeCall(array2, start, end)) {
    start = 0;
    end = length;
  } else {
    start = start == null ? 0 : toInteger(start);
    end = end === void 0 ? length : toInteger(end);
  }
  return baseSlice(array2, start, end);
}
var snakeCase = createCompounder(function(result2, word, index) {
  return result2 + (index ? "_" : "") + word.toLowerCase();
});
function baseSome(collection2, predicate) {
  var result2;
  baseEach(collection2, function(value, index, collection3) {
    result2 = predicate(value, index, collection3);
    return !result2;
  });
  return !!result2;
}
function some(collection2, predicate, guard) {
  var func2 = isArray$2(collection2) ? arraySome : baseSome;
  if (guard && isIterateeCall(collection2, predicate, guard)) {
    predicate = void 0;
  }
  return func2(collection2, baseIteratee(predicate));
}
var sortBy = baseRest(function(collection2, iteratees) {
  if (collection2 == null) {
    return [];
  }
  var length = iteratees.length;
  if (length > 1 && isIterateeCall(collection2, iteratees[0], iteratees[1])) {
    iteratees = [];
  } else if (length > 2 && isIterateeCall(iteratees[0], iteratees[1], iteratees[2])) {
    iteratees = [iteratees[0]];
  }
  return baseOrderBy(collection2, baseFlatten(iteratees, 1), []);
});
var MAX_ARRAY_LENGTH$2 = 4294967295, MAX_ARRAY_INDEX = MAX_ARRAY_LENGTH$2 - 1;
var nativeFloor$3 = Math.floor, nativeMin$a = Math.min;
function baseSortedIndexBy(array2, value, iteratee2, retHighest) {
  var low = 0, high = array2 == null ? 0 : array2.length;
  if (high === 0) {
    return 0;
  }
  value = iteratee2(value);
  var valIsNaN = value !== value, valIsNull = value === null, valIsSymbol = isSymbol(value), valIsUndefined = value === void 0;
  while (low < high) {
    var mid = nativeFloor$3((low + high) / 2), computed = iteratee2(array2[mid]), othIsDefined = computed !== void 0, othIsNull = computed === null, othIsReflexive = computed === computed, othIsSymbol = isSymbol(computed);
    if (valIsNaN) {
      var setLow = retHighest || othIsReflexive;
    } else if (valIsUndefined) {
      setLow = othIsReflexive && (retHighest || othIsDefined);
    } else if (valIsNull) {
      setLow = othIsReflexive && othIsDefined && (retHighest || !othIsNull);
    } else if (valIsSymbol) {
      setLow = othIsReflexive && othIsDefined && !othIsNull && (retHighest || !othIsSymbol);
    } else if (othIsNull || othIsSymbol) {
      setLow = false;
    } else {
      setLow = retHighest ? computed <= value : computed < value;
    }
    if (setLow) {
      low = mid + 1;
    } else {
      high = mid;
    }
  }
  return nativeMin$a(high, MAX_ARRAY_INDEX);
}
var MAX_ARRAY_LENGTH$3 = 4294967295, HALF_MAX_ARRAY_LENGTH = MAX_ARRAY_LENGTH$3 >>> 1;
function baseSortedIndex(array2, value, retHighest) {
  var low = 0, high = array2 == null ? low : array2.length;
  if (typeof value == "number" && value === value && high <= HALF_MAX_ARRAY_LENGTH) {
    while (low < high) {
      var mid = low + high >>> 1, computed = array2[mid];
      if (computed !== null && !isSymbol(computed) && (retHighest ? computed <= value : computed < value)) {
        low = mid + 1;
      } else {
        high = mid;
      }
    }
    return high;
  }
  return baseSortedIndexBy(array2, value, identity$1, retHighest);
}
function sortedIndex(array2, value) {
  return baseSortedIndex(array2, value);
}
function sortedIndexBy(array2, value, iteratee2) {
  return baseSortedIndexBy(array2, value, baseIteratee(iteratee2));
}
function sortedIndexOf(array2, value) {
  var length = array2 == null ? 0 : array2.length;
  if (length) {
    var index = baseSortedIndex(array2, value);
    if (index < length && eq(array2[index], value)) {
      return index;
    }
  }
  return -1;
}
function sortedLastIndex(array2, value) {
  return baseSortedIndex(array2, value, true);
}
function sortedLastIndexBy(array2, value, iteratee2) {
  return baseSortedIndexBy(array2, value, baseIteratee(iteratee2), true);
}
function sortedLastIndexOf(array2, value) {
  var length = array2 == null ? 0 : array2.length;
  if (length) {
    var index = baseSortedIndex(array2, value, true) - 1;
    if (eq(array2[index], value)) {
      return index;
    }
  }
  return -1;
}
function baseSortedUniq(array2, iteratee2) {
  var index = -1, length = array2.length, resIndex = 0, result2 = [];
  while (++index < length) {
    var value = array2[index], computed = iteratee2 ? iteratee2(value) : value;
    if (!index || !eq(computed, seen)) {
      var seen = computed;
      result2[resIndex++] = value === 0 ? 0 : value;
    }
  }
  return result2;
}
function sortedUniq(array2) {
  return array2 && array2.length ? baseSortedUniq(array2) : [];
}
function sortedUniqBy(array2, iteratee2) {
  return array2 && array2.length ? baseSortedUniq(array2, baseIteratee(iteratee2)) : [];
}
var MAX_ARRAY_LENGTH$4 = 4294967295;
function split(string2, separator, limit) {
  if (limit && typeof limit != "number" && isIterateeCall(string2, separator, limit)) {
    separator = limit = void 0;
  }
  limit = limit === void 0 ? MAX_ARRAY_LENGTH$4 : limit >>> 0;
  if (!limit) {
    return [];
  }
  string2 = toString$2(string2);
  if (string2 && (typeof separator == "string" || separator != null && !isRegExp$1(separator))) {
    separator = baseToString(separator);
    if (!separator && hasUnicode(string2)) {
      return castSlice(stringToArray(string2), 0, limit);
    }
  }
  return string2.split(separator, limit);
}
var FUNC_ERROR_TEXT$a = "Expected a function";
var nativeMax$d = Math.max;
function spread$1(func2, start) {
  if (typeof func2 != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$a);
  }
  start = start == null ? 0 : nativeMax$d(toInteger(start), 0);
  return baseRest(function(args) {
    var array2 = args[start], otherArgs = castSlice(args, 0, start);
    if (array2) {
      arrayPush(otherArgs, array2);
    }
    return apply(func2, this, otherArgs);
  });
}
var startCase = createCompounder(function(result2, word, index) {
  return result2 + (index ? " " : "") + upperFirst(word);
});
function startsWith(string2, target, position) {
  string2 = toString$2(string2);
  position = position == null ? 0 : baseClamp(toInteger(position), 0, string2.length);
  target = baseToString(target);
  return string2.slice(position, position + target.length) == target;
}
function stubObject() {
  return {};
}
function stubString() {
  return "";
}
function stubTrue() {
  return true;
}
var subtract = createMathOperation(function(minuend, subtrahend) {
  return minuend - subtrahend;
}, 0);
function sum(array2) {
  return array2 && array2.length ? baseSum(array2, identity$1) : 0;
}
function sumBy(array2, iteratee2) {
  return array2 && array2.length ? baseSum(array2, baseIteratee(iteratee2)) : 0;
}
function tail(array2) {
  var length = array2 == null ? 0 : array2.length;
  return length ? baseSlice(array2, 1, length) : [];
}
function take(array2, n, guard) {
  if (!(array2 && array2.length)) {
    return [];
  }
  n = guard || n === void 0 ? 1 : toInteger(n);
  return baseSlice(array2, 0, n < 0 ? 0 : n);
}
function takeRight(array2, n, guard) {
  var length = array2 == null ? 0 : array2.length;
  if (!length) {
    return [];
  }
  n = guard || n === void 0 ? 1 : toInteger(n);
  n = length - n;
  return baseSlice(array2, n < 0 ? 0 : n, length);
}
function takeRightWhile(array2, predicate) {
  return array2 && array2.length ? baseWhile(array2, baseIteratee(predicate), false, true) : [];
}
function takeWhile(array2, predicate) {
  return array2 && array2.length ? baseWhile(array2, baseIteratee(predicate)) : [];
}
function tap(value, interceptor) {
  interceptor(value);
  return value;
}
var objectProto$q = Object.prototype;
var hasOwnProperty$m = objectProto$q.hasOwnProperty;
function customDefaultsAssignIn(objValue, srcValue, key, object2) {
  if (objValue === void 0 || eq(objValue, objectProto$q[key]) && !hasOwnProperty$m.call(object2, key)) {
    return srcValue;
  }
  return objValue;
}
var stringEscapes = {
  "\\": "\\",
  "'": "'",
  "\n": "n",
  "\r": "r",
  "\u2028": "u2028",
  "\u2029": "u2029"
};
function escapeStringChar(chr) {
  return "\\" + stringEscapes[chr];
}
var reInterpolate = /<%=([\s\S]+?)%>/g;
var reEscape = /<%-([\s\S]+?)%>/g;
var reEvaluate = /<%([\s\S]+?)%>/g;
var templateSettings = {
  escape: reEscape,
  evaluate: reEvaluate,
  interpolate: reInterpolate,
  variable: "",
  imports: {
    _: {escape}
  }
};
var INVALID_TEMPL_VAR_ERROR_TEXT = "Invalid `variable` option passed into `_.template`";
var reEmptyStringLeading = /\b__p \+= '';/g, reEmptyStringMiddle = /\b(__p \+=) '' \+/g, reEmptyStringTrailing = /(__e\(.*?\)|\b__t\)) \+\n'';/g;
var reForbiddenIdentifierChars = /[()=,{}\[\]\/\s]/;
var reEsTemplate = /\$\{([^\\}]*(?:\\.[^\\}]*)*)\}/g;
var reNoMatch = /($^)/;
var reUnescapedString = /['\n\r\u2028\u2029\\]/g;
var objectProto$r = Object.prototype;
var hasOwnProperty$n = objectProto$r.hasOwnProperty;
function template(string2, options, guard) {
  var settings = templateSettings.imports._.templateSettings || templateSettings;
  if (guard && isIterateeCall(string2, options, guard)) {
    options = void 0;
  }
  string2 = toString$2(string2);
  options = assignInWith({}, options, settings, customDefaultsAssignIn);
  var imports = assignInWith({}, options.imports, settings.imports, customDefaultsAssignIn), importsKeys = keys(imports), importsValues = baseValues(imports, importsKeys);
  var isEscaping, isEvaluating, index = 0, interpolate = options.interpolate || reNoMatch, source = "__p += '";
  var reDelimiters = RegExp((options.escape || reNoMatch).source + "|" + interpolate.source + "|" + (interpolate === reInterpolate ? reEsTemplate : reNoMatch).source + "|" + (options.evaluate || reNoMatch).source + "|$", "g");
  var sourceURL = hasOwnProperty$n.call(options, "sourceURL") ? "//# sourceURL=" + (options.sourceURL + "").replace(/\s/g, " ") + "\n" : "";
  string2.replace(reDelimiters, function(match, escapeValue, interpolateValue, esTemplateValue, evaluateValue, offset) {
    interpolateValue || (interpolateValue = esTemplateValue);
    source += string2.slice(index, offset).replace(reUnescapedString, escapeStringChar);
    if (escapeValue) {
      isEscaping = true;
      source += "' +\n__e(" + escapeValue + ") +\n'";
    }
    if (evaluateValue) {
      isEvaluating = true;
      source += "';\n" + evaluateValue + ";\n__p += '";
    }
    if (interpolateValue) {
      source += "' +\n((__t = (" + interpolateValue + ")) == null ? '' : __t) +\n'";
    }
    index = offset + match.length;
    return match;
  });
  source += "';\n";
  var variable = hasOwnProperty$n.call(options, "variable") && options.variable;
  if (!variable) {
    source = "with (obj) {\n" + source + "\n}\n";
  } else if (reForbiddenIdentifierChars.test(variable)) {
    throw new Error(INVALID_TEMPL_VAR_ERROR_TEXT);
  }
  source = (isEvaluating ? source.replace(reEmptyStringLeading, "") : source).replace(reEmptyStringMiddle, "$1").replace(reEmptyStringTrailing, "$1;");
  source = "function(" + (variable || "obj") + ") {\n" + (variable ? "" : "obj || (obj = {});\n") + "var __t, __p = ''" + (isEscaping ? ", __e = _.escape" : "") + (isEvaluating ? ", __j = Array.prototype.join;\nfunction print() { __p += __j.call(arguments, '') }\n" : ";\n") + source + "return __p\n}";
  var result2 = attempt(function() {
    return Function(importsKeys, sourceURL + "return " + source).apply(void 0, importsValues);
  });
  result2.source = source;
  if (isError(result2)) {
    throw result2;
  }
  return result2;
}
var FUNC_ERROR_TEXT$b = "Expected a function";
function throttle(func2, wait, options) {
  var leading = true, trailing = true;
  if (typeof func2 != "function") {
    throw new TypeError(FUNC_ERROR_TEXT$b);
  }
  if (isObject$1(options)) {
    leading = "leading" in options ? !!options.leading : leading;
    trailing = "trailing" in options ? !!options.trailing : trailing;
  }
  return debounce(func2, wait, {
    leading,
    maxWait: wait,
    trailing
  });
}
function thru(value, interceptor) {
  return interceptor(value);
}
var MAX_SAFE_INTEGER$4 = 9007199254740991;
var MAX_ARRAY_LENGTH$5 = 4294967295;
var nativeMin$b = Math.min;
function times(n, iteratee2) {
  n = toInteger(n);
  if (n < 1 || n > MAX_SAFE_INTEGER$4) {
    return [];
  }
  var index = MAX_ARRAY_LENGTH$5, length = nativeMin$b(n, MAX_ARRAY_LENGTH$5);
  iteratee2 = castFunction(iteratee2);
  n -= MAX_ARRAY_LENGTH$5;
  var result2 = baseTimes(length, iteratee2);
  while (++index < n) {
    iteratee2(index);
  }
  return result2;
}
function wrapperToIterator() {
  return this;
}
function baseWrapperValue(value, actions) {
  var result2 = value;
  if (result2 instanceof LazyWrapper) {
    result2 = result2.value();
  }
  return arrayReduce(actions, function(result3, action) {
    return action.func.apply(action.thisArg, arrayPush([result3], action.args));
  }, result2);
}
function wrapperValue() {
  return baseWrapperValue(this.__wrapped__, this.__actions__);
}
function toLower(value) {
  return toString$2(value).toLowerCase();
}
function toPath(value) {
  if (isArray$2(value)) {
    return arrayMap(value, toKey);
  }
  return isSymbol(value) ? [value] : copyArray(stringToPath(toString$2(value)));
}
var MAX_SAFE_INTEGER$5 = 9007199254740991;
function toSafeInteger(value) {
  return value ? baseClamp(toInteger(value), -MAX_SAFE_INTEGER$5, MAX_SAFE_INTEGER$5) : value === 0 ? value : 0;
}
function toUpper(value) {
  return toString$2(value).toUpperCase();
}
function transform(object2, iteratee2, accumulator) {
  var isArr = isArray$2(object2), isArrLike = isArr || isBuffer$2(object2) || isTypedArray$1(object2);
  iteratee2 = baseIteratee(iteratee2);
  if (accumulator == null) {
    var Ctor = object2 && object2.constructor;
    if (isArrLike) {
      accumulator = isArr ? new Ctor() : [];
    } else if (isObject$1(object2)) {
      accumulator = isFunction$1(Ctor) ? baseCreate(getPrototype(object2)) : {};
    } else {
      accumulator = {};
    }
  }
  (isArrLike ? arrayEach : baseForOwn)(object2, function(value, index, object3) {
    return iteratee2(accumulator, value, index, object3);
  });
  return accumulator;
}
function charsEndIndex(strSymbols, chrSymbols) {
  var index = strSymbols.length;
  while (index-- && baseIndexOf(chrSymbols, strSymbols[index], 0) > -1) {
  }
  return index;
}
function charsStartIndex(strSymbols, chrSymbols) {
  var index = -1, length = strSymbols.length;
  while (++index < length && baseIndexOf(chrSymbols, strSymbols[index], 0) > -1) {
  }
  return index;
}
function trim$1(string2, chars, guard) {
  string2 = toString$2(string2);
  if (string2 && (guard || chars === void 0)) {
    return baseTrim(string2);
  }
  if (!string2 || !(chars = baseToString(chars))) {
    return string2;
  }
  var strSymbols = stringToArray(string2), chrSymbols = stringToArray(chars), start = charsStartIndex(strSymbols, chrSymbols), end = charsEndIndex(strSymbols, chrSymbols) + 1;
  return castSlice(strSymbols, start, end).join("");
}
function trimEnd(string2, chars, guard) {
  string2 = toString$2(string2);
  if (string2 && (guard || chars === void 0)) {
    return string2.slice(0, trimmedEndIndex(string2) + 1);
  }
  if (!string2 || !(chars = baseToString(chars))) {
    return string2;
  }
  var strSymbols = stringToArray(string2), end = charsEndIndex(strSymbols, stringToArray(chars)) + 1;
  return castSlice(strSymbols, 0, end).join("");
}
var reTrimStart$2 = /^\s+/;
function trimStart(string2, chars, guard) {
  string2 = toString$2(string2);
  if (string2 && (guard || chars === void 0)) {
    return string2.replace(reTrimStart$2, "");
  }
  if (!string2 || !(chars = baseToString(chars))) {
    return string2;
  }
  var strSymbols = stringToArray(string2), start = charsStartIndex(strSymbols, stringToArray(chars));
  return castSlice(strSymbols, start).join("");
}
var DEFAULT_TRUNC_LENGTH = 30, DEFAULT_TRUNC_OMISSION = "...";
var reFlags$1 = /\w*$/;
function truncate(string2, options) {
  var length = DEFAULT_TRUNC_LENGTH, omission = DEFAULT_TRUNC_OMISSION;
  if (isObject$1(options)) {
    var separator = "separator" in options ? options.separator : separator;
    length = "length" in options ? toInteger(options.length) : length;
    omission = "omission" in options ? baseToString(options.omission) : omission;
  }
  string2 = toString$2(string2);
  var strLength = string2.length;
  if (hasUnicode(string2)) {
    var strSymbols = stringToArray(string2);
    strLength = strSymbols.length;
  }
  if (length >= strLength) {
    return string2;
  }
  var end = length - stringSize(omission);
  if (end < 1) {
    return omission;
  }
  var result2 = strSymbols ? castSlice(strSymbols, 0, end).join("") : string2.slice(0, end);
  if (separator === void 0) {
    return result2 + omission;
  }
  if (strSymbols) {
    end += result2.length - end;
  }
  if (isRegExp$1(separator)) {
    if (string2.slice(end).search(separator)) {
      var match, substring = result2;
      if (!separator.global) {
        separator = RegExp(separator.source, toString$2(reFlags$1.exec(separator)) + "g");
      }
      separator.lastIndex = 0;
      while (match = separator.exec(substring)) {
        var newEnd = match.index;
      }
      result2 = result2.slice(0, newEnd === void 0 ? end : newEnd);
    }
  } else if (string2.indexOf(baseToString(separator), end) != end) {
    var index = result2.lastIndexOf(separator);
    if (index > -1) {
      result2 = result2.slice(0, index);
    }
  }
  return result2 + omission;
}
function unary(func2) {
  return ary(func2, 1);
}
var htmlUnescapes = {
  "&amp;": "&",
  "&lt;": "<",
  "&gt;": ">",
  "&quot;": '"',
  "&#39;": "'"
};
var unescapeHtmlChar = basePropertyOf(htmlUnescapes);
var reEscapedHtml = /&(?:amp|lt|gt|quot|#39);/g, reHasEscapedHtml = RegExp(reEscapedHtml.source);
function unescape$1(string2) {
  string2 = toString$2(string2);
  return string2 && reHasEscapedHtml.test(string2) ? string2.replace(reEscapedHtml, unescapeHtmlChar) : string2;
}
var INFINITY$5 = 1 / 0;
var createSet = !(Set$1 && 1 / setToArray(new Set$1([, -0]))[1] == INFINITY$5) ? noop$2 : function(values2) {
  return new Set$1(values2);
};
var LARGE_ARRAY_SIZE$2 = 200;
function baseUniq(array2, iteratee2, comparator) {
  var index = -1, includes2 = arrayIncludes, length = array2.length, isCommon = true, result2 = [], seen = result2;
  if (comparator) {
    isCommon = false;
    includes2 = arrayIncludesWith;
  } else if (length >= LARGE_ARRAY_SIZE$2) {
    var set2 = iteratee2 ? null : createSet(array2);
    if (set2) {
      return setToArray(set2);
    }
    isCommon = false;
    includes2 = cacheHas;
    seen = new SetCache();
  } else {
    seen = iteratee2 ? [] : result2;
  }
  outer:
    while (++index < length) {
      var value = array2[index], computed = iteratee2 ? iteratee2(value) : value;
      value = comparator || value !== 0 ? value : 0;
      if (isCommon && computed === computed) {
        var seenIndex = seen.length;
        while (seenIndex--) {
          if (seen[seenIndex] === computed) {
            continue outer;
          }
        }
        if (iteratee2) {
          seen.push(computed);
        }
        result2.push(value);
      } else if (!includes2(seen, computed, comparator)) {
        if (seen !== result2) {
          seen.push(computed);
        }
        result2.push(value);
      }
    }
  return result2;
}
var union = baseRest(function(arrays) {
  return baseUniq(baseFlatten(arrays, 1, isArrayLikeObject, true));
});
var unionBy = baseRest(function(arrays) {
  var iteratee2 = last(arrays);
  if (isArrayLikeObject(iteratee2)) {
    iteratee2 = void 0;
  }
  return baseUniq(baseFlatten(arrays, 1, isArrayLikeObject, true), baseIteratee(iteratee2));
});
var unionWith = baseRest(function(arrays) {
  var comparator = last(arrays);
  comparator = typeof comparator == "function" ? comparator : void 0;
  return baseUniq(baseFlatten(arrays, 1, isArrayLikeObject, true), void 0, comparator);
});
function uniq(array2) {
  return array2 && array2.length ? baseUniq(array2) : [];
}
function uniqBy(array2, iteratee2) {
  return array2 && array2.length ? baseUniq(array2, baseIteratee(iteratee2)) : [];
}
function uniqWith(array2, comparator) {
  comparator = typeof comparator == "function" ? comparator : void 0;
  return array2 && array2.length ? baseUniq(array2, void 0, comparator) : [];
}
var idCounter$1 = 0;
function uniqueId(prefix) {
  var id = ++idCounter$1;
  return toString$2(prefix) + id;
}
function unset(object2, path) {
  return object2 == null ? true : baseUnset(object2, path);
}
var nativeMax$e = Math.max;
function unzip(array2) {
  if (!(array2 && array2.length)) {
    return [];
  }
  var length = 0;
  array2 = arrayFilter(array2, function(group) {
    if (isArrayLikeObject(group)) {
      length = nativeMax$e(group.length, length);
      return true;
    }
  });
  return baseTimes(length, function(index) {
    return arrayMap(array2, baseProperty(index));
  });
}
function unzipWith(array2, iteratee2) {
  if (!(array2 && array2.length)) {
    return [];
  }
  var result2 = unzip(array2);
  if (iteratee2 == null) {
    return result2;
  }
  return arrayMap(result2, function(group) {
    return apply(iteratee2, void 0, group);
  });
}
function baseUpdate(object2, path, updater, customizer) {
  return baseSet(object2, path, updater(baseGet(object2, path)), customizer);
}
function update$1(object2, path, updater) {
  return object2 == null ? object2 : baseUpdate(object2, path, castFunction(updater));
}
function updateWith(object2, path, updater, customizer) {
  customizer = typeof customizer == "function" ? customizer : void 0;
  return object2 == null ? object2 : baseUpdate(object2, path, castFunction(updater), customizer);
}
var upperCase = createCompounder(function(result2, word, index) {
  return result2 + (index ? " " : "") + word.toUpperCase();
});
function valuesIn(object2) {
  return object2 == null ? [] : baseValues(object2, keysIn(object2));
}
var without = baseRest(function(array2, values2) {
  return isArrayLikeObject(array2) ? baseDifference(array2, values2) : [];
});
function wrap(value, wrapper) {
  return partial(castFunction(wrapper), value);
}
var wrapperAt = flatRest(function(paths) {
  var length = paths.length, start = length ? paths[0] : 0, value = this.__wrapped__, interceptor = function(object2) {
    return baseAt(object2, paths);
  };
  if (length > 1 || this.__actions__.length || !(value instanceof LazyWrapper) || !isIndex(start)) {
    return this.thru(interceptor);
  }
  value = value.slice(start, +start + (length ? 1 : 0));
  value.__actions__.push({
    func: thru,
    args: [interceptor],
    thisArg: void 0
  });
  return new LodashWrapper(value, this.__chain__).thru(function(array2) {
    if (length && !array2.length) {
      array2.push(void 0);
    }
    return array2;
  });
});
function wrapperChain() {
  return chain(this);
}
function wrapperReverse() {
  var value = this.__wrapped__;
  if (value instanceof LazyWrapper) {
    var wrapped = value;
    if (this.__actions__.length) {
      wrapped = new LazyWrapper(this);
    }
    wrapped = wrapped.reverse();
    wrapped.__actions__.push({
      func: thru,
      args: [reverse],
      thisArg: void 0
    });
    return new LodashWrapper(wrapped, this.__chain__);
  }
  return this.thru(reverse);
}
function baseXor(arrays, iteratee2, comparator) {
  var length = arrays.length;
  if (length < 2) {
    return length ? baseUniq(arrays[0]) : [];
  }
  var index = -1, result2 = Array(length);
  while (++index < length) {
    var array2 = arrays[index], othIndex = -1;
    while (++othIndex < length) {
      if (othIndex != index) {
        result2[index] = baseDifference(result2[index] || array2, arrays[othIndex], iteratee2, comparator);
      }
    }
  }
  return baseUniq(baseFlatten(result2, 1), iteratee2, comparator);
}
var xor = baseRest(function(arrays) {
  return baseXor(arrayFilter(arrays, isArrayLikeObject));
});
var xorBy = baseRest(function(arrays) {
  var iteratee2 = last(arrays);
  if (isArrayLikeObject(iteratee2)) {
    iteratee2 = void 0;
  }
  return baseXor(arrayFilter(arrays, isArrayLikeObject), baseIteratee(iteratee2));
});
var xorWith = baseRest(function(arrays) {
  var comparator = last(arrays);
  comparator = typeof comparator == "function" ? comparator : void 0;
  return baseXor(arrayFilter(arrays, isArrayLikeObject), void 0, comparator);
});
var zip = baseRest(unzip);
function baseZipObject(props, values2, assignFunc) {
  var index = -1, length = props.length, valsLength = values2.length, result2 = {};
  while (++index < length) {
    var value = index < valsLength ? values2[index] : void 0;
    assignFunc(result2, props[index], value);
  }
  return result2;
}
function zipObject(props, values2) {
  return baseZipObject(props || [], values2 || [], assignValue);
}
function zipObjectDeep(props, values2) {
  return baseZipObject(props || [], values2 || [], baseSet);
}
var zipWith = baseRest(function(arrays) {
  var length = arrays.length, iteratee2 = length > 1 ? arrays[length - 1] : void 0;
  iteratee2 = typeof iteratee2 == "function" ? (arrays.pop(), iteratee2) : void 0;
  return unzipWith(arrays, iteratee2);
});
var array = {
  chunk,
  compact,
  concat,
  difference,
  differenceBy,
  differenceWith,
  drop,
  dropRight,
  dropRightWhile,
  dropWhile,
  fill,
  findIndex,
  findLastIndex,
  first: head,
  flatten,
  flattenDeep,
  flattenDepth,
  fromPairs,
  head,
  indexOf,
  initial,
  intersection,
  intersectionBy,
  intersectionWith,
  join,
  last,
  lastIndexOf,
  nth,
  pull,
  pullAll,
  pullAllBy,
  pullAllWith,
  pullAt,
  remove,
  reverse,
  slice,
  sortedIndex,
  sortedIndexBy,
  sortedIndexOf,
  sortedLastIndex,
  sortedLastIndexBy,
  sortedLastIndexOf,
  sortedUniq,
  sortedUniqBy,
  tail,
  take,
  takeRight,
  takeRightWhile,
  takeWhile,
  union,
  unionBy,
  unionWith,
  uniq,
  uniqBy,
  uniqWith,
  unzip,
  unzipWith,
  without,
  xor,
  xorBy,
  xorWith,
  zip,
  zipObject,
  zipObjectDeep,
  zipWith
};
var collection = {
  countBy,
  each: forEach$1,
  eachRight: forEachRight,
  every,
  filter,
  find,
  findLast,
  flatMap,
  flatMapDeep,
  flatMapDepth,
  forEach: forEach$1,
  forEachRight,
  groupBy,
  includes,
  invokeMap,
  keyBy,
  map,
  orderBy,
  partition,
  reduce,
  reduceRight,
  reject,
  sample,
  sampleSize,
  shuffle,
  size,
  some,
  sortBy
};
var date = {
  now: now$1
};
var func = {
  after,
  ary,
  before,
  bind: bind$1,
  bindKey,
  curry,
  curryRight,
  debounce,
  defer,
  delay,
  flip,
  memoize,
  negate,
  once,
  overArgs,
  partial,
  partialRight,
  rearg,
  rest,
  spread: spread$1,
  throttle,
  unary,
  wrap
};
var lang = {
  castArray,
  clone,
  cloneDeep,
  cloneDeepWith,
  cloneWith,
  conformsTo,
  eq,
  gt,
  gte,
  isArguments,
  isArray: isArray$2,
  isArrayBuffer: isArrayBuffer$1,
  isArrayLike,
  isArrayLikeObject,
  isBoolean: isBoolean$1,
  isBuffer: isBuffer$2,
  isDate: isDate$1,
  isElement,
  isEmpty,
  isEqual,
  isEqualWith,
  isError,
  isFinite: isFinite$1,
  isFunction: isFunction$1,
  isInteger,
  isLength,
  isMap,
  isMatch,
  isMatchWith,
  isNaN: isNaN$1,
  isNative,
  isNil,
  isNull,
  isNumber: isNumber$1,
  isObject: isObject$1,
  isObjectLike,
  isPlainObject: isPlainObject$1,
  isRegExp: isRegExp$1,
  isSafeInteger,
  isSet,
  isString: isString$1,
  isSymbol,
  isTypedArray: isTypedArray$1,
  isUndefined: isUndefined$1,
  isWeakMap,
  isWeakSet,
  lt,
  lte,
  toArray: toArray$1,
  toFinite,
  toInteger,
  toLength,
  toNumber,
  toPlainObject,
  toSafeInteger,
  toString: toString$2
};
var math = {
  add,
  ceil,
  divide,
  floor,
  max,
  maxBy,
  mean,
  meanBy,
  min,
  minBy,
  multiply,
  round,
  subtract,
  sum,
  sumBy
};
var number = {
  clamp,
  inRange,
  random
};
var object = {
  assign: assign$1,
  assignIn,
  assignInWith,
  assignWith,
  at,
  create,
  defaults: defaults$1,
  defaultsDeep,
  entries: toPairs,
  entriesIn: toPairsIn,
  extend: assignIn,
  extendWith: assignInWith,
  findKey: findKey$1,
  findLastKey,
  forIn,
  forInRight,
  forOwn,
  forOwnRight,
  functions,
  functionsIn,
  get,
  has,
  hasIn,
  invert,
  invertBy,
  invoke,
  keys,
  keysIn,
  mapKeys,
  mapValues,
  merge: merge$1,
  mergeWith,
  omit,
  omitBy,
  pick,
  pickBy,
  result,
  set,
  setWith,
  toPairs,
  toPairsIn,
  transform,
  unset,
  update: update$1,
  updateWith,
  values,
  valuesIn
};
var seq = {
  at: wrapperAt,
  chain,
  commit: wrapperCommit,
  lodash,
  next: wrapperNext,
  plant: wrapperPlant,
  reverse: wrapperReverse,
  tap,
  thru,
  toIterator: wrapperToIterator,
  toJSON: wrapperValue,
  value: wrapperValue,
  valueOf: wrapperValue,
  wrapperChain
};
var string = {
  camelCase,
  capitalize,
  deburr,
  endsWith: endsWith$1,
  escape,
  escapeRegExp,
  kebabCase,
  lowerCase,
  lowerFirst,
  pad,
  padEnd,
  padStart,
  parseInt: parseInt$1,
  repeat,
  replace,
  snakeCase,
  split,
  startCase,
  startsWith,
  template,
  templateSettings,
  toLower,
  toUpper,
  trim: trim$1,
  trimEnd,
  trimStart,
  truncate,
  unescape: unescape$1,
  upperCase,
  upperFirst,
  words
};
var util = {
  attempt,
  bindAll,
  cond,
  conforms,
  constant,
  defaultTo,
  flow,
  flowRight,
  identity: identity$1,
  iteratee,
  matches,
  matchesProperty,
  method,
  methodOf,
  mixin,
  noop: noop$2,
  nthArg,
  over,
  overEvery,
  overSome,
  property,
  propertyOf,
  range,
  rangeRight,
  stubArray,
  stubFalse,
  stubObject,
  stubString,
  stubTrue,
  times,
  toPath,
  uniqueId
};
function lazyClone() {
  var result2 = new LazyWrapper(this.__wrapped__);
  result2.__actions__ = copyArray(this.__actions__);
  result2.__dir__ = this.__dir__;
  result2.__filtered__ = this.__filtered__;
  result2.__iteratees__ = copyArray(this.__iteratees__);
  result2.__takeCount__ = this.__takeCount__;
  result2.__views__ = copyArray(this.__views__);
  return result2;
}
function lazyReverse() {
  if (this.__filtered__) {
    var result2 = new LazyWrapper(this);
    result2.__dir__ = -1;
    result2.__filtered__ = true;
  } else {
    result2 = this.clone();
    result2.__dir__ *= -1;
  }
  return result2;
}
var nativeMax$f = Math.max, nativeMin$c = Math.min;
function getView(start, end, transforms) {
  var index = -1, length = transforms.length;
  while (++index < length) {
    var data = transforms[index], size2 = data.size;
    switch (data.type) {
      case "drop":
        start += size2;
        break;
      case "dropRight":
        end -= size2;
        break;
      case "take":
        end = nativeMin$c(end, start + size2);
        break;
      case "takeRight":
        start = nativeMax$f(start, end - size2);
        break;
    }
  }
  return {start, end};
}
var LAZY_FILTER_FLAG = 1, LAZY_MAP_FLAG = 2;
var nativeMin$d = Math.min;
function lazyValue() {
  var array2 = this.__wrapped__.value(), dir = this.__dir__, isArr = isArray$2(array2), isRight = dir < 0, arrLength = isArr ? array2.length : 0, view = getView(0, arrLength, this.__views__), start = view.start, end = view.end, length = end - start, index = isRight ? end : start - 1, iteratees = this.__iteratees__, iterLength = iteratees.length, resIndex = 0, takeCount = nativeMin$d(length, this.__takeCount__);
  if (!isArr || !isRight && arrLength == length && takeCount == length) {
    return baseWrapperValue(array2, this.__actions__);
  }
  var result2 = [];
  outer:
    while (length-- && resIndex < takeCount) {
      index += dir;
      var iterIndex = -1, value = array2[index];
      while (++iterIndex < iterLength) {
        var data = iteratees[iterIndex], iteratee2 = data.iteratee, type = data.type, computed = iteratee2(value);
        if (type == LAZY_MAP_FLAG) {
          value = computed;
        } else if (!computed) {
          if (type == LAZY_FILTER_FLAG) {
            continue outer;
          } else {
            break outer;
          }
        }
      }
      result2[resIndex++] = value;
    }
  return result2;
}
/**
 * @license
 * Lodash (Custom Build) <https://lodash.com/>
 * Build: `lodash modularize exports="es" -o ./`
 * Copyright OpenJS Foundation and other contributors <https://openjsf.org/>
 * Released under MIT license <https://lodash.com/license>
 * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
 * Copyright Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
 */
var VERSION$1 = "4.17.21";
var WRAP_BIND_KEY_FLAG$6 = 2;
var LAZY_FILTER_FLAG$1 = 1, LAZY_WHILE_FLAG = 3;
var MAX_ARRAY_LENGTH$6 = 4294967295;
var arrayProto$5 = Array.prototype, objectProto$s = Object.prototype;
var hasOwnProperty$o = objectProto$s.hasOwnProperty;
var symIterator$1 = Symbol$1 ? Symbol$1.iterator : void 0;
var nativeMax$g = Math.max, nativeMin$e = Math.min;
var mixin$1 = function(func2) {
  return function(object2, source, options) {
    if (options == null) {
      var isObj = isObject$1(source), props = isObj && keys(source), methodNames = props && props.length && baseFunctions(source, props);
      if (!(methodNames ? methodNames.length : isObj)) {
        options = source;
        source = object2;
        object2 = this;
      }
    }
    return func2(object2, source, options);
  };
}(mixin);
lodash.after = func.after;
lodash.ary = func.ary;
lodash.assign = object.assign;
lodash.assignIn = object.assignIn;
lodash.assignInWith = object.assignInWith;
lodash.assignWith = object.assignWith;
lodash.at = object.at;
lodash.before = func.before;
lodash.bind = func.bind;
lodash.bindAll = util.bindAll;
lodash.bindKey = func.bindKey;
lodash.castArray = lang.castArray;
lodash.chain = seq.chain;
lodash.chunk = array.chunk;
lodash.compact = array.compact;
lodash.concat = array.concat;
lodash.cond = util.cond;
lodash.conforms = util.conforms;
lodash.constant = util.constant;
lodash.countBy = collection.countBy;
lodash.create = object.create;
lodash.curry = func.curry;
lodash.curryRight = func.curryRight;
lodash.debounce = func.debounce;
lodash.defaults = object.defaults;
lodash.defaultsDeep = object.defaultsDeep;
lodash.defer = func.defer;
lodash.delay = func.delay;
lodash.difference = array.difference;
lodash.differenceBy = array.differenceBy;
lodash.differenceWith = array.differenceWith;
lodash.drop = array.drop;
lodash.dropRight = array.dropRight;
lodash.dropRightWhile = array.dropRightWhile;
lodash.dropWhile = array.dropWhile;
lodash.fill = array.fill;
lodash.filter = collection.filter;
lodash.flatMap = collection.flatMap;
lodash.flatMapDeep = collection.flatMapDeep;
lodash.flatMapDepth = collection.flatMapDepth;
lodash.flatten = array.flatten;
lodash.flattenDeep = array.flattenDeep;
lodash.flattenDepth = array.flattenDepth;
lodash.flip = func.flip;
lodash.flow = util.flow;
lodash.flowRight = util.flowRight;
lodash.fromPairs = array.fromPairs;
lodash.functions = object.functions;
lodash.functionsIn = object.functionsIn;
lodash.groupBy = collection.groupBy;
lodash.initial = array.initial;
lodash.intersection = array.intersection;
lodash.intersectionBy = array.intersectionBy;
lodash.intersectionWith = array.intersectionWith;
lodash.invert = object.invert;
lodash.invertBy = object.invertBy;
lodash.invokeMap = collection.invokeMap;
lodash.iteratee = util.iteratee;
lodash.keyBy = collection.keyBy;
lodash.keys = keys;
lodash.keysIn = object.keysIn;
lodash.map = collection.map;
lodash.mapKeys = object.mapKeys;
lodash.mapValues = object.mapValues;
lodash.matches = util.matches;
lodash.matchesProperty = util.matchesProperty;
lodash.memoize = func.memoize;
lodash.merge = object.merge;
lodash.mergeWith = object.mergeWith;
lodash.method = util.method;
lodash.methodOf = util.methodOf;
lodash.mixin = mixin$1;
lodash.negate = negate;
lodash.nthArg = util.nthArg;
lodash.omit = object.omit;
lodash.omitBy = object.omitBy;
lodash.once = func.once;
lodash.orderBy = collection.orderBy;
lodash.over = util.over;
lodash.overArgs = func.overArgs;
lodash.overEvery = util.overEvery;
lodash.overSome = util.overSome;
lodash.partial = func.partial;
lodash.partialRight = func.partialRight;
lodash.partition = collection.partition;
lodash.pick = object.pick;
lodash.pickBy = object.pickBy;
lodash.property = util.property;
lodash.propertyOf = util.propertyOf;
lodash.pull = array.pull;
lodash.pullAll = array.pullAll;
lodash.pullAllBy = array.pullAllBy;
lodash.pullAllWith = array.pullAllWith;
lodash.pullAt = array.pullAt;
lodash.range = util.range;
lodash.rangeRight = util.rangeRight;
lodash.rearg = func.rearg;
lodash.reject = collection.reject;
lodash.remove = array.remove;
lodash.rest = func.rest;
lodash.reverse = array.reverse;
lodash.sampleSize = collection.sampleSize;
lodash.set = object.set;
lodash.setWith = object.setWith;
lodash.shuffle = collection.shuffle;
lodash.slice = array.slice;
lodash.sortBy = collection.sortBy;
lodash.sortedUniq = array.sortedUniq;
lodash.sortedUniqBy = array.sortedUniqBy;
lodash.split = string.split;
lodash.spread = func.spread;
lodash.tail = array.tail;
lodash.take = array.take;
lodash.takeRight = array.takeRight;
lodash.takeRightWhile = array.takeRightWhile;
lodash.takeWhile = array.takeWhile;
lodash.tap = seq.tap;
lodash.throttle = func.throttle;
lodash.thru = thru;
lodash.toArray = lang.toArray;
lodash.toPairs = object.toPairs;
lodash.toPairsIn = object.toPairsIn;
lodash.toPath = util.toPath;
lodash.toPlainObject = lang.toPlainObject;
lodash.transform = object.transform;
lodash.unary = func.unary;
lodash.union = array.union;
lodash.unionBy = array.unionBy;
lodash.unionWith = array.unionWith;
lodash.uniq = array.uniq;
lodash.uniqBy = array.uniqBy;
lodash.uniqWith = array.uniqWith;
lodash.unset = object.unset;
lodash.unzip = array.unzip;
lodash.unzipWith = array.unzipWith;
lodash.update = object.update;
lodash.updateWith = object.updateWith;
lodash.values = object.values;
lodash.valuesIn = object.valuesIn;
lodash.without = array.without;
lodash.words = string.words;
lodash.wrap = func.wrap;
lodash.xor = array.xor;
lodash.xorBy = array.xorBy;
lodash.xorWith = array.xorWith;
lodash.zip = array.zip;
lodash.zipObject = array.zipObject;
lodash.zipObjectDeep = array.zipObjectDeep;
lodash.zipWith = array.zipWith;
lodash.entries = object.toPairs;
lodash.entriesIn = object.toPairsIn;
lodash.extend = object.assignIn;
lodash.extendWith = object.assignInWith;
mixin$1(lodash, lodash);
lodash.add = math.add;
lodash.attempt = util.attempt;
lodash.camelCase = string.camelCase;
lodash.capitalize = string.capitalize;
lodash.ceil = math.ceil;
lodash.clamp = number.clamp;
lodash.clone = lang.clone;
lodash.cloneDeep = lang.cloneDeep;
lodash.cloneDeepWith = lang.cloneDeepWith;
lodash.cloneWith = lang.cloneWith;
lodash.conformsTo = lang.conformsTo;
lodash.deburr = string.deburr;
lodash.defaultTo = util.defaultTo;
lodash.divide = math.divide;
lodash.endsWith = string.endsWith;
lodash.eq = lang.eq;
lodash.escape = string.escape;
lodash.escapeRegExp = string.escapeRegExp;
lodash.every = collection.every;
lodash.find = collection.find;
lodash.findIndex = array.findIndex;
lodash.findKey = object.findKey;
lodash.findLast = collection.findLast;
lodash.findLastIndex = array.findLastIndex;
lodash.findLastKey = object.findLastKey;
lodash.floor = math.floor;
lodash.forEach = collection.forEach;
lodash.forEachRight = collection.forEachRight;
lodash.forIn = object.forIn;
lodash.forInRight = object.forInRight;
lodash.forOwn = object.forOwn;
lodash.forOwnRight = object.forOwnRight;
lodash.get = object.get;
lodash.gt = lang.gt;
lodash.gte = lang.gte;
lodash.has = object.has;
lodash.hasIn = object.hasIn;
lodash.head = array.head;
lodash.identity = identity$1;
lodash.includes = collection.includes;
lodash.indexOf = array.indexOf;
lodash.inRange = number.inRange;
lodash.invoke = object.invoke;
lodash.isArguments = lang.isArguments;
lodash.isArray = isArray$2;
lodash.isArrayBuffer = lang.isArrayBuffer;
lodash.isArrayLike = lang.isArrayLike;
lodash.isArrayLikeObject = lang.isArrayLikeObject;
lodash.isBoolean = lang.isBoolean;
lodash.isBuffer = lang.isBuffer;
lodash.isDate = lang.isDate;
lodash.isElement = lang.isElement;
lodash.isEmpty = lang.isEmpty;
lodash.isEqual = lang.isEqual;
lodash.isEqualWith = lang.isEqualWith;
lodash.isError = lang.isError;
lodash.isFinite = lang.isFinite;
lodash.isFunction = lang.isFunction;
lodash.isInteger = lang.isInteger;
lodash.isLength = lang.isLength;
lodash.isMap = lang.isMap;
lodash.isMatch = lang.isMatch;
lodash.isMatchWith = lang.isMatchWith;
lodash.isNaN = lang.isNaN;
lodash.isNative = lang.isNative;
lodash.isNil = lang.isNil;
lodash.isNull = lang.isNull;
lodash.isNumber = lang.isNumber;
lodash.isObject = isObject$1;
lodash.isObjectLike = lang.isObjectLike;
lodash.isPlainObject = lang.isPlainObject;
lodash.isRegExp = lang.isRegExp;
lodash.isSafeInteger = lang.isSafeInteger;
lodash.isSet = lang.isSet;
lodash.isString = lang.isString;
lodash.isSymbol = lang.isSymbol;
lodash.isTypedArray = lang.isTypedArray;
lodash.isUndefined = lang.isUndefined;
lodash.isWeakMap = lang.isWeakMap;
lodash.isWeakSet = lang.isWeakSet;
lodash.join = array.join;
lodash.kebabCase = string.kebabCase;
lodash.last = last;
lodash.lastIndexOf = array.lastIndexOf;
lodash.lowerCase = string.lowerCase;
lodash.lowerFirst = string.lowerFirst;
lodash.lt = lang.lt;
lodash.lte = lang.lte;
lodash.max = math.max;
lodash.maxBy = math.maxBy;
lodash.mean = math.mean;
lodash.meanBy = math.meanBy;
lodash.min = math.min;
lodash.minBy = math.minBy;
lodash.stubArray = util.stubArray;
lodash.stubFalse = util.stubFalse;
lodash.stubObject = util.stubObject;
lodash.stubString = util.stubString;
lodash.stubTrue = util.stubTrue;
lodash.multiply = math.multiply;
lodash.nth = array.nth;
lodash.noop = util.noop;
lodash.now = date.now;
lodash.pad = string.pad;
lodash.padEnd = string.padEnd;
lodash.padStart = string.padStart;
lodash.parseInt = string.parseInt;
lodash.random = number.random;
lodash.reduce = collection.reduce;
lodash.reduceRight = collection.reduceRight;
lodash.repeat = string.repeat;
lodash.replace = string.replace;
lodash.result = object.result;
lodash.round = math.round;
lodash.sample = collection.sample;
lodash.size = collection.size;
lodash.snakeCase = string.snakeCase;
lodash.some = collection.some;
lodash.sortedIndex = array.sortedIndex;
lodash.sortedIndexBy = array.sortedIndexBy;
lodash.sortedIndexOf = array.sortedIndexOf;
lodash.sortedLastIndex = array.sortedLastIndex;
lodash.sortedLastIndexBy = array.sortedLastIndexBy;
lodash.sortedLastIndexOf = array.sortedLastIndexOf;
lodash.startCase = string.startCase;
lodash.startsWith = string.startsWith;
lodash.subtract = math.subtract;
lodash.sum = math.sum;
lodash.sumBy = math.sumBy;
lodash.template = string.template;
lodash.times = util.times;
lodash.toFinite = lang.toFinite;
lodash.toInteger = toInteger;
lodash.toLength = lang.toLength;
lodash.toLower = string.toLower;
lodash.toNumber = lang.toNumber;
lodash.toSafeInteger = lang.toSafeInteger;
lodash.toString = lang.toString;
lodash.toUpper = string.toUpper;
lodash.trim = string.trim;
lodash.trimEnd = string.trimEnd;
lodash.trimStart = string.trimStart;
lodash.truncate = string.truncate;
lodash.unescape = string.unescape;
lodash.uniqueId = util.uniqueId;
lodash.upperCase = string.upperCase;
lodash.upperFirst = string.upperFirst;
lodash.each = collection.forEach;
lodash.eachRight = collection.forEachRight;
lodash.first = array.head;
mixin$1(lodash, function() {
  var source = {};
  baseForOwn(lodash, function(func2, methodName) {
    if (!hasOwnProperty$o.call(lodash.prototype, methodName)) {
      source[methodName] = func2;
    }
  });
  return source;
}(), {chain: false});
lodash.VERSION = VERSION$1;
(lodash.templateSettings = string.templateSettings).imports._ = lodash;
arrayEach(["bind", "bindKey", "curry", "curryRight", "partial", "partialRight"], function(methodName) {
  lodash[methodName].placeholder = lodash;
});
arrayEach(["drop", "take"], function(methodName, index) {
  LazyWrapper.prototype[methodName] = function(n) {
    n = n === void 0 ? 1 : nativeMax$g(toInteger(n), 0);
    var result2 = this.__filtered__ && !index ? new LazyWrapper(this) : this.clone();
    if (result2.__filtered__) {
      result2.__takeCount__ = nativeMin$e(n, result2.__takeCount__);
    } else {
      result2.__views__.push({
        size: nativeMin$e(n, MAX_ARRAY_LENGTH$6),
        type: methodName + (result2.__dir__ < 0 ? "Right" : "")
      });
    }
    return result2;
  };
  LazyWrapper.prototype[methodName + "Right"] = function(n) {
    return this.reverse()[methodName](n).reverse();
  };
});
arrayEach(["filter", "map", "takeWhile"], function(methodName, index) {
  var type = index + 1, isFilter = type == LAZY_FILTER_FLAG$1 || type == LAZY_WHILE_FLAG;
  LazyWrapper.prototype[methodName] = function(iteratee2) {
    var result2 = this.clone();
    result2.__iteratees__.push({
      iteratee: baseIteratee(iteratee2),
      type
    });
    result2.__filtered__ = result2.__filtered__ || isFilter;
    return result2;
  };
});
arrayEach(["head", "last"], function(methodName, index) {
  var takeName = "take" + (index ? "Right" : "");
  LazyWrapper.prototype[methodName] = function() {
    return this[takeName](1).value()[0];
  };
});
arrayEach(["initial", "tail"], function(methodName, index) {
  var dropName = "drop" + (index ? "" : "Right");
  LazyWrapper.prototype[methodName] = function() {
    return this.__filtered__ ? new LazyWrapper(this) : this[dropName](1);
  };
});
LazyWrapper.prototype.compact = function() {
  return this.filter(identity$1);
};
LazyWrapper.prototype.find = function(predicate) {
  return this.filter(predicate).head();
};
LazyWrapper.prototype.findLast = function(predicate) {
  return this.reverse().find(predicate);
};
LazyWrapper.prototype.invokeMap = baseRest(function(path, args) {
  if (typeof path == "function") {
    return new LazyWrapper(this);
  }
  return this.map(function(value) {
    return baseInvoke(value, path, args);
  });
});
LazyWrapper.prototype.reject = function(predicate) {
  return this.filter(negate(baseIteratee(predicate)));
};
LazyWrapper.prototype.slice = function(start, end) {
  start = toInteger(start);
  var result2 = this;
  if (result2.__filtered__ && (start > 0 || end < 0)) {
    return new LazyWrapper(result2);
  }
  if (start < 0) {
    result2 = result2.takeRight(-start);
  } else if (start) {
    result2 = result2.drop(start);
  }
  if (end !== void 0) {
    end = toInteger(end);
    result2 = end < 0 ? result2.dropRight(-end) : result2.take(end - start);
  }
  return result2;
};
LazyWrapper.prototype.takeRightWhile = function(predicate) {
  return this.reverse().takeWhile(predicate).reverse();
};
LazyWrapper.prototype.toArray = function() {
  return this.take(MAX_ARRAY_LENGTH$6);
};
baseForOwn(LazyWrapper.prototype, function(func2, methodName) {
  var checkIteratee = /^(?:filter|find|map|reject)|While$/.test(methodName), isTaker = /^(?:head|last)$/.test(methodName), lodashFunc = lodash[isTaker ? "take" + (methodName == "last" ? "Right" : "") : methodName], retUnwrapped = isTaker || /^find/.test(methodName);
  if (!lodashFunc) {
    return;
  }
  lodash.prototype[methodName] = function() {
    var value = this.__wrapped__, args = isTaker ? [1] : arguments, isLazy = value instanceof LazyWrapper, iteratee2 = args[0], useLazy = isLazy || isArray$2(value);
    var interceptor = function(value2) {
      var result3 = lodashFunc.apply(lodash, arrayPush([value2], args));
      return isTaker && chainAll ? result3[0] : result3;
    };
    if (useLazy && checkIteratee && typeof iteratee2 == "function" && iteratee2.length != 1) {
      isLazy = useLazy = false;
    }
    var chainAll = this.__chain__, isHybrid = !!this.__actions__.length, isUnwrapped = retUnwrapped && !chainAll, onlyLazy = isLazy && !isHybrid;
    if (!retUnwrapped && useLazy) {
      value = onlyLazy ? value : new LazyWrapper(this);
      var result2 = func2.apply(value, args);
      result2.__actions__.push({func: thru, args: [interceptor], thisArg: void 0});
      return new LodashWrapper(result2, chainAll);
    }
    if (isUnwrapped && onlyLazy) {
      return func2.apply(this, args);
    }
    result2 = this.thru(interceptor);
    return isUnwrapped ? isTaker ? result2.value()[0] : result2.value() : result2;
  };
});
arrayEach(["pop", "push", "shift", "sort", "splice", "unshift"], function(methodName) {
  var func2 = arrayProto$5[methodName], chainName = /^(?:push|sort|unshift)$/.test(methodName) ? "tap" : "thru", retUnwrapped = /^(?:pop|shift)$/.test(methodName);
  lodash.prototype[methodName] = function() {
    var args = arguments;
    if (retUnwrapped && !this.__chain__) {
      var value = this.value();
      return func2.apply(isArray$2(value) ? value : [], args);
    }
    return this[chainName](function(value2) {
      return func2.apply(isArray$2(value2) ? value2 : [], args);
    });
  };
});
baseForOwn(LazyWrapper.prototype, function(func2, methodName) {
  var lodashFunc = lodash[methodName];
  if (lodashFunc) {
    var key = lodashFunc.name + "";
    if (!hasOwnProperty$o.call(realNames, key)) {
      realNames[key] = [];
    }
    realNames[key].push({name: methodName, func: lodashFunc});
  }
});
realNames[createHybrid(void 0, WRAP_BIND_KEY_FLAG$6).name] = [{
  name: "wrapper",
  func: void 0
}];
LazyWrapper.prototype.clone = lazyClone;
LazyWrapper.prototype.reverse = lazyReverse;
LazyWrapper.prototype.value = lazyValue;
lodash.prototype.at = seq.at;
lodash.prototype.chain = seq.wrapperChain;
lodash.prototype.commit = seq.commit;
lodash.prototype.next = seq.next;
lodash.prototype.plant = seq.plant;
lodash.prototype.reverse = seq.reverse;
lodash.prototype.toJSON = lodash.prototype.valueOf = lodash.prototype.value = seq.value;
lodash.prototype.first = lodash.prototype.head;
if (symIterator$1) {
  lodash.prototype[symIterator$1] = seq.toIterator;
}

/* generated by Svelte v3.58.0 */

function create_if_block_5$1(ctx) {
	let h2;
	let raw_value = /*subheading*/ ctx[1].html + "";
	let mounted;
	let dispose;

	return {
		c() {
			h2 = element("h2");
			this.h();
		},
		l(nodes) {
			h2 = claim_element(nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			h2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "subheading svelte-17457rs");
		},
		m(target, anchor) {
			insert_hydration(target, h2, anchor);
			h2.innerHTML = raw_value;

			if (!mounted) {
				dispose = listen(h2, "keyup", keyup_handler);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*subheading*/ 2 && raw_value !== (raw_value = /*subheading*/ ctx[1].html + "")) h2.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(h2);
			mounted = false;
			dispose();
		}
	};
}

// (480:0) {#if videoModalVisible}
function create_if_block_4$1(ctx) {
	let div3;
	let div0;
	let t;
	let div2;
	let div1;
	let iframe;
	let iframe_src_value;
	let div3_transition;
	let current;
	let mounted;
	let dispose;

	return {
		c() {
			div3 = element("div");
			div0 = element("div");
			t = space();
			div2 = element("div");
			div1 = element("div");
			iframe = element("iframe");
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { id: true, class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			children(div0).forEach(detach);
			t = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { style: true });
			var div1_nodes = children(div1);

			iframe = claim_element(div1_nodes, "IFRAME", {
				src: true,
				frameborder: true,
				allow: true,
				style: true,
				title: true,
				class: true
			});

			children(iframe).forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "bg svelte-17457rs");
			if (!src_url_equal(iframe.src, iframe_src_value = "https://player.vimeo.com/video/777551197?h=4342f0b1c9&badge=0&autopause=0&player_id=0&app_id=58479")) attr(iframe, "src", iframe_src_value);
			attr(iframe, "frameborder", "0");
			attr(iframe, "allow", "autoplay; fullscreen; picture-in-picture");
			iframe.allowFullscreen = true;
			set_style(iframe, "position", "absolute");
			set_style(iframe, "top", "0");
			set_style(iframe, "left", "0");
			set_style(iframe, "width", "100%");
			set_style(iframe, "height", "100%");
			attr(iframe, "title", "Primo Walkthrough");
			attr(iframe, "class", "svelte-17457rs");
			set_style(div1, "padding", "62.5% 0 0 0");
			set_style(div1, "position", "relative");
			attr(div2, "class", "container has-video svelte-17457rs");
			attr(div3, "id", "modal");
			attr(div3, "class", "svelte-17457rs");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div0);
			append_hydration(div3, t);
			append_hydration(div3, div2);
			append_hydration(div2, div1);
			append_hydration(div1, iframe);
			current = true;

			if (!mounted) {
				dispose = [
					listen(div0, "click", /*hideModal*/ ctx[8]),
					listen(div0, "keyup", keyup_handler_1)
				];

				mounted = true;
			}
		},
		p: noop,
		i(local) {
			if (current) return;

			add_render_callback(() => {
				if (!current) return;
				if (!div3_transition) div3_transition = create_bidirectional_transition(div3, fade, { duration: 200 }, true);
				div3_transition.run(1);
			});

			current = true;
		},
		o(local) {
			if (!div3_transition) div3_transition = create_bidirectional_transition(div3, fade, { duration: 200 }, false);
			div3_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			if (detaching && div3_transition) div3_transition.end();
			mounted = false;
			run_all(dispose);
		}
	};
}

// (488:0) {#if modalVisible}
function create_if_block$2(ctx) {
	let div3;
	let div0;
	let t0;
	let div2;
	let div1;
	let span;
	let t1_value = /*modal*/ ctx[3].title + "";
	let t1;
	let t2;
	let t3_value = /*currentPlatform*/ ctx[7].name + "";
	let t3;
	let t4;
	let html_tag;
	let raw_value = /*currentPlatform*/ ctx[7].svg + "";
	let t5;
	let div3_transition;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (!/*downloading*/ ctx[6]) return create_if_block_1$2;
		return create_else_block$2;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			div3 = element("div");
			div0 = element("div");
			t0 = space();
			div2 = element("div");
			div1 = element("div");
			span = element("span");
			t1 = text(t1_value);
			t2 = space();
			t3 = text(t3_value);
			t4 = space();
			html_tag = new HtmlTagHydration(false);
			t5 = space();
			if_block.c();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { id: true, class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			children(div0).forEach(detach);
			t0 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			span = claim_element(div1_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, t1_value);
			t2 = claim_space(span_nodes);
			t3 = claim_text(span_nodes, t3_value);
			span_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			html_tag = claim_html_tag(div1_nodes, false);
			div1_nodes.forEach(detach);
			t5 = claim_space(div2_nodes);
			if_block.l(div2_nodes);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "bg svelte-17457rs");
			attr(span, "class", "svelte-17457rs");
			html_tag.a = null;
			attr(div1, "class", "title svelte-17457rs");
			attr(div2, "class", "container svelte-17457rs");
			attr(div3, "id", "modal");
			attr(div3, "class", "svelte-17457rs");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div0);
			append_hydration(div3, t0);
			append_hydration(div3, div2);
			append_hydration(div2, div1);
			append_hydration(div1, span);
			append_hydration(span, t1);
			append_hydration(span, t2);
			append_hydration(span, t3);
			append_hydration(div1, t4);
			html_tag.m(raw_value, div1);
			append_hydration(div2, t5);
			if_block.m(div2, null);
			current = true;

			if (!mounted) {
				dispose = [
					listen(div0, "click", /*hideModal*/ ctx[8]),
					listen(div0, "keyup", keyup_handler_2)
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*modal*/ 8) && t1_value !== (t1_value = /*modal*/ ctx[3].title + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*currentPlatform*/ 128) && t3_value !== (t3_value = /*currentPlatform*/ ctx[7].name + "")) set_data(t3, t3_value);
			if ((!current || dirty & /*currentPlatform*/ 128) && raw_value !== (raw_value = /*currentPlatform*/ ctx[7].svg + "")) html_tag.p(raw_value);

			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(div2, null);
				}
			}
		},
		i(local) {
			if (current) return;

			add_render_callback(() => {
				if (!current) return;
				if (!div3_transition) div3_transition = create_bidirectional_transition(div3, fade, { duration: 200 }, true);
				div3_transition.run(1);
			});

			current = true;
		},
		o(local) {
			if (!div3_transition) div3_transition = create_bidirectional_transition(div3, fade, { duration: 200 }, false);
			div3_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			if_block.d();
			if (detaching && div3_transition) div3_transition.end();
			mounted = false;
			run_all(dispose);
		}
	};
}

// (520:4) {:else}
function create_else_block$2(ctx) {
	let div0;
	let raw_value = /*modal*/ ctx[3].downloading_content + "";
	let t0;
	let div12;
	let div11;
	let div10;
	let div9;
	let div6;
	let form;
	let div3;
	let div2;
	let div1;
	let input0;
	let t1;
	let input1;
	let t2;
	let div5;
	let button0;
	let t3;
	let t4;
	let button1;
	let div4;
	let t5;
	let span;
	let t6;
	let t7;
	let input2;
	let t8;
	let div8;
	let div7;
	let h4;
	let t9;
	let t10;
	let p;
	let t11;
	let t12;
	let script0;
	let t13;
	let t14;
	let img;
	let img_src_value;
	let t15;
	let script1;
	let script1_src_value;

	return {
		c() {
			div0 = element("div");
			t0 = space();
			div12 = element("div");
			div11 = element("div");
			div10 = element("div");
			div9 = element("div");
			div6 = element("div");
			form = element("form");
			div3 = element("div");
			div2 = element("div");
			div1 = element("div");
			input0 = element("input");
			t1 = space();
			input1 = element("input");
			t2 = space();
			div5 = element("div");
			button0 = element("button");
			t3 = text("Subscribe");
			t4 = space();
			button1 = element("button");
			div4 = element("div");
			t5 = space();
			span = element("span");
			t6 = text("Loading...");
			t7 = space();
			input2 = element("input");
			t8 = space();
			div8 = element("div");
			div7 = element("div");
			h4 = element("h4");
			t9 = text("Thank you!");
			t10 = space();
			p = element("p");
			t11 = text("You have successfully joined our subscriber list.");
			t12 = space();
			script0 = element("script");
			t13 = text("function ml_webform_success_5039306(){var r=ml_jQuery||jQuery;r(\".ml-subscribe-form-5039306 .row-success\").show(),r(\".ml-subscribe-form-5039306 .row-form\").hide()}");
			t14 = space();
			img = element("img");
			t15 = space();
			script1 = element("script");
			this.h();
		},
		l(nodes) {
			div0 = claim_element(nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t0 = claim_space(nodes);
			div12 = claim_element(nodes, "DIV", { class: true });
			var div12_nodes = children(div12);
			div11 = claim_element(div12_nodes, "DIV", { id: true, class: true });
			var div11_nodes = children(div11);
			div10 = claim_element(div11_nodes, "DIV", { class: true });
			var div10_nodes = children(div10);
			div9 = claim_element(div10_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			div6 = claim_element(div9_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);

			form = claim_element(div6_nodes, "FORM", {
				class: true,
				action: true,
				"data-code": true,
				method: true,
				target: true
			});

			var form_nodes = children(form);
			div3 = claim_element(form_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			input0 = claim_element(div1_nodes, "INPUT", {
				"aria-label": true,
				"aria-required": true,
				type: true,
				class: true,
				"data-inputmask": true,
				name: true,
				placeholder: true,
				autocomplete: true
			});

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t1 = claim_space(form_nodes);
			input1 = claim_element(form_nodes, "INPUT", { type: true, name: true, class: true });
			t2 = claim_space(form_nodes);
			div5 = claim_element(form_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			button0 = claim_element(div5_nodes, "BUTTON", { type: true, class: true });
			var button0_nodes = children(button0);
			t3 = claim_text(button0_nodes, "Subscribe");
			button0_nodes.forEach(detach);
			t4 = claim_space(div5_nodes);
			button1 = claim_element(div5_nodes, "BUTTON", { style: true, type: true, class: true });
			var button1_nodes = children(button1);
			div4 = claim_element(button1_nodes, "DIV", { class: true });
			children(div4).forEach(detach);
			t5 = claim_space(button1_nodes);
			span = claim_element(button1_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t6 = claim_text(span_nodes, "Loading...");
			span_nodes.forEach(detach);
			button1_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			t7 = claim_space(form_nodes);
			input2 = claim_element(form_nodes, "INPUT", { type: true, name: true, class: true });
			form_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			t8 = claim_space(div9_nodes);
			div8 = claim_element(div9_nodes, "DIV", { class: true, style: true });
			var div8_nodes = children(div8);
			div7 = claim_element(div8_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			h4 = claim_element(div7_nodes, "H4", {});
			var h4_nodes = children(h4);
			t9 = claim_text(h4_nodes, "Thank you!");
			h4_nodes.forEach(detach);
			t10 = claim_space(div7_nodes);
			p = claim_element(div7_nodes, "P", {});
			var p_nodes = children(p);
			t11 = claim_text(p_nodes, "You have successfully joined our subscriber list.");
			p_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			div11_nodes.forEach(detach);
			div12_nodes.forEach(detach);
			t12 = claim_space(nodes);
			script0 = claim_element(nodes, "SCRIPT", {});
			var script0_nodes = children(script0);
			t13 = claim_text(script0_nodes, "function ml_webform_success_5039306(){var r=ml_jQuery||jQuery;r(\".ml-subscribe-form-5039306 .row-success\").show(),r(\".ml-subscribe-form-5039306 .row-form\").hide()}");
			script0_nodes.forEach(detach);
			t14 = claim_space(nodes);

			img = claim_element(nodes, "IMG", {
				src: true,
				width: true,
				height: true,
				style: true,
				alt: true,
				border: true
			});

			t15 = claim_space(nodes);
			script1 = claim_element(nodes, "SCRIPT", { src: true, type: true });
			var script1_nodes = children(script1);
			script1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "content svelte-17457rs");
			attr(input0, "aria-label", "email");
			attr(input0, "aria-required", "true");
			attr(input0, "type", "email");
			attr(input0, "class", "form-control svelte-17457rs");
			attr(input0, "data-inputmask", "");
			attr(input0, "name", "fields[email]");
			attr(input0, "placeholder", "Email");
			attr(input0, "autocomplete", "email");
			attr(div1, "class", "ml-field-group ml-field-email ml-validate-email ml-validate-required");
			attr(div2, "class", "ml-form-fieldRow ml-last-item");
			attr(div3, "class", "ml-form-formContent");
			attr(input1, "type", "hidden");
			attr(input1, "name", "ml-submit");
			input1.value = "1";
			attr(input1, "class", "svelte-17457rs");
			attr(button0, "type", "submit");
			attr(button0, "class", "primary button svelte-17457rs");
			attr(div4, "class", "ml-form-embedSubmitLoad");
			attr(span, "class", "sr-only svelte-17457rs");
			button1.disabled = "disabled";
			set_style(button1, "display", "none");
			attr(button1, "type", "button");
			attr(button1, "class", "loading svelte-17457rs");
			attr(div5, "class", "ml-form-embedSubmit");
			attr(input2, "type", "hidden");
			attr(input2, "name", "anticsrf");
			input2.value = "true";
			attr(input2, "class", "svelte-17457rs");
			attr(form, "class", "ml-block-form svelte-17457rs");
			attr(form, "action", "https://static.mailerlite.com/webforms/submit/j2m2z7");
			attr(form, "data-code", "j2m2z7");
			attr(form, "method", "post");
			attr(form, "target", "_blank");
			attr(div6, "class", "ml-form-embedBody ml-form-embedBodyDefault row-form");
			attr(div7, "class", "ml-form-successContent");
			attr(div8, "class", "ml-form-successBody row-success");
			set_style(div8, "display", "none");
			attr(div9, "class", "ml-form-embedWrapper embedForm");
			attr(div10, "class", "ml-form-align-center");
			attr(div11, "id", "mlb2-5039306");
			attr(div11, "class", "ml-form-embedContainer ml-subscribe-form ml-subscribe-form-5039306");
			attr(div12, "class", "form");
			if (!src_url_equal(img.src, img_src_value = "https://track.mailerlite.com/webforms/o/5039306/j2m2z7?v1637419080")) attr(img, "src", img_src_value);
			attr(img, "width", "1");
			attr(img, "height", "1");
			set_style(img, "max-width", "1px");
			set_style(img, "max-height", "1px");
			set_style(img, "visibility", "hidden");
			set_style(img, "padding", "0");
			set_style(img, "margin", "0");
			set_style(img, "display", "block");
			attr(img, "alt", ".");
			attr(img, "border", "0");
			if (!src_url_equal(script1.src, script1_src_value = "https://static.mailerlite.com/js/w/webforms.min.js?v0c75f831c56857441820dcec3163967c")) attr(script1, "src", script1_src_value);
			attr(script1, "type", "text/javascript");
		},
		m(target, anchor) {
			insert_hydration(target, div0, anchor);
			div0.innerHTML = raw_value;
			insert_hydration(target, t0, anchor);
			insert_hydration(target, div12, anchor);
			append_hydration(div12, div11);
			append_hydration(div11, div10);
			append_hydration(div10, div9);
			append_hydration(div9, div6);
			append_hydration(div6, form);
			append_hydration(form, div3);
			append_hydration(div3, div2);
			append_hydration(div2, div1);
			append_hydration(div1, input0);
			append_hydration(form, t1);
			append_hydration(form, input1);
			append_hydration(form, t2);
			append_hydration(form, div5);
			append_hydration(div5, button0);
			append_hydration(button0, t3);
			append_hydration(div5, t4);
			append_hydration(div5, button1);
			append_hydration(button1, div4);
			append_hydration(button1, t5);
			append_hydration(button1, span);
			append_hydration(span, t6);
			append_hydration(form, t7);
			append_hydration(form, input2);
			append_hydration(div9, t8);
			append_hydration(div9, div8);
			append_hydration(div8, div7);
			append_hydration(div7, h4);
			append_hydration(h4, t9);
			append_hydration(div7, t10);
			append_hydration(div7, p);
			append_hydration(p, t11);
			insert_hydration(target, t12, anchor);
			insert_hydration(target, script0, anchor);
			append_hydration(script0, t13);
			insert_hydration(target, t14, anchor);
			insert_hydration(target, img, anchor);
			insert_hydration(target, t15, anchor);
			insert_hydration(target, script1, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*modal*/ 8 && raw_value !== (raw_value = /*modal*/ ctx[3].downloading_content + "")) div0.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(div0);
			if (detaching) detach(t0);
			if (detaching) detach(div12);
			if (detaching) detach(t12);
			if (detaching) detach(script0);
			if (detaching) detach(t14);
			if (detaching) detach(img);
			if (detaching) detach(t15);
			if (detaching) detach(script1);
		}
	};
}

// (496:4) {#if !downloading}
function create_if_block_1$2(ctx) {
	let div;
	let raw_value = /*modal*/ ctx[3].content + "";
	let t0;
	let t1;
	let if_block1_anchor;
	let if_block0 = /*currentPlatform*/ ctx[7].description && create_if_block_3$1(ctx);
	let if_block1 = !/*currentPlatform*/ ctx[7].disabled && create_if_block_2$1(ctx);

	return {
		c() {
			div = element("div");
			t0 = space();
			if (if_block0) if_block0.c();
			t1 = space();
			if (if_block1) if_block1.c();
			if_block1_anchor = empty();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			div_nodes.forEach(detach);
			t0 = claim_space(nodes);
			if (if_block0) if_block0.l(nodes);
			t1 = claim_space(nodes);
			if (if_block1) if_block1.l(nodes);
			if_block1_anchor = empty();
			this.h();
		},
		h() {
			attr(div, "class", "content svelte-17457rs");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			div.innerHTML = raw_value;
			insert_hydration(target, t0, anchor);
			if (if_block0) if_block0.m(target, anchor);
			insert_hydration(target, t1, anchor);
			if (if_block1) if_block1.m(target, anchor);
			insert_hydration(target, if_block1_anchor, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*modal*/ 8 && raw_value !== (raw_value = /*modal*/ ctx[3].content + "")) div.innerHTML = raw_value;
			if (/*currentPlatform*/ ctx[7].description) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_3$1(ctx);
					if_block0.c();
					if_block0.m(t1.parentNode, t1);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (!/*currentPlatform*/ ctx[7].disabled) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_2$1(ctx);
					if_block1.c();
					if_block1.m(if_block1_anchor.parentNode, if_block1_anchor);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}
		},
		d(detaching) {
			if (detaching) detach(div);
			if (detaching) detach(t0);
			if (if_block0) if_block0.d(detaching);
			if (detaching) detach(t1);
			if (if_block1) if_block1.d(detaching);
			if (detaching) detach(if_block1_anchor);
		}
	};
}

// (498:6) {#if currentPlatform.description}
function create_if_block_3$1(ctx) {
	let div;
	let raw_value = /*currentPlatform*/ ctx[7].description + "";

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "content svelte-17457rs");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			div.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*currentPlatform*/ 128 && raw_value !== (raw_value = /*currentPlatform*/ ctx[7].description + "")) div.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (509:6) {#if !currentPlatform.disabled}
function create_if_block_2$1(ctx) {
	let a;
	let span;
	let t0_value = /*modal*/ ctx[3].title + "";
	let t0;
	let t1;
	let t2_value = /*currentPlatform*/ ctx[7].name + "";
	let t2;
	let t3;
	let svg;
	let path;
	let a_href_value;
	let mounted;
	let dispose;

	return {
		c() {
			a = element("a");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			t2 = text(t2_value);
			t3 = space();
			svg = svg_element("svg");
			path = svg_element("path");
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true, download: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			t1 = claim_space(span_nodes);
			t2 = claim_text(span_nodes, t2_value);
			span_nodes.forEach(detach);
			t3 = claim_space(a_nodes);

			svg = claim_svg_element(a_nodes, "svg", {
				width: true,
				height: true,
				viewBox: true,
				fill: true,
				xmlns: true
			});

			var svg_nodes = children(svg);
			path = claim_svg_element(svg_nodes, "path", { d: true, fill: true });
			children(path).forEach(detach);
			svg_nodes.forEach(detach);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-17457rs");
			attr(path, "d", "M18.75 13.75H13.5352L11.7676 15.5176C11.2969 15.9883 10.668 16.25 10 16.25C9.33203 16.25 8.70469 15.99 8.23242 15.5176L6.46484 13.75H1.25C0.559766 13.75 0 14.3098 0 15V18.75C0 19.4402 0.559766 20 1.25 20H18.75C19.4402 20 20 19.4402 20 18.75V15C20 14.3086 19.4414 13.75 18.75 13.75ZM16.875 17.8125C16.3594 17.8125 15.9375 17.3906 15.9375 16.875C15.9375 16.3594 16.3594 15.9375 16.875 15.9375C17.3906 15.9375 17.8125 16.3594 17.8125 16.875C17.8125 17.3906 17.3906 17.8125 16.875 17.8125ZM9.11719 14.6328C9.35938 14.8789 9.67969 15 10 15C10.3203 15 10.6398 14.8779 10.8836 14.6338L15.8836 9.63379C16.3715 9.14551 16.3715 8.35449 15.8836 7.86621C15.3953 7.37793 14.6039 7.37793 14.116 7.86621L11.25 10.7344V1.25C11.25 0.559766 10.6902 0 10 0C9.30859 0 8.75 0.559766 8.75 1.25V10.7344L5.88281 7.86719C5.39492 7.37891 4.60352 7.37891 4.11523 7.86719C3.62734 8.35547 3.62734 9.14648 4.11523 9.63477L9.11719 14.6328Z");
			attr(path, "fill", "#E6E6E6");
			attr(svg, "width", "20");
			attr(svg, "height", "20");
			attr(svg, "viewBox", "0 0 20 20");
			attr(svg, "fill", "none");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(a, "class", "button svelte-17457rs");
			attr(a, "href", a_href_value = /*currentPlatform*/ ctx[7].download_link);
			attr(a, "download", "");
			toggle_class(a, "disabled", !consented);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, span);
			append_hydration(span, t0);
			append_hydration(span, t1);
			append_hydration(span, t2);
			append_hydration(a, t3);
			append_hydration(a, svg);
			append_hydration(svg, path);

			if (!mounted) {
				dispose = listen(a, "click", /*click_handler*/ ctx[16]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*modal*/ 8 && t0_value !== (t0_value = /*modal*/ ctx[3].title + "")) set_data(t0, t0_value);
			if (dirty & /*currentPlatform*/ 128 && t2_value !== (t2_value = /*currentPlatform*/ ctx[7].name + "")) set_data(t2, t2_value);

			if (dirty & /*currentPlatform*/ 128 && a_href_value !== (a_href_value = /*currentPlatform*/ ctx[7].download_link)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$3(ctx) {
	let div6;
	let div5;
	let header;
	let div0;
	let t0;
	let div3;
	let h1;
	let raw_value = /*heading*/ ctx[0].html + "";
	let t1;
	let div1;
	let t2;
	let a0;
	let icon0;
	let t3;
	let a1;
	let icon1;
	let t4;
	let a2;
	let icon2;
	let t5;
	let t6;
	let div2;
	let a3;
	let t7;
	let icon3;
	let t8;
	let div4;
	let figure;
	let iframe;
	let iframe_src_value;
	let t9;
	let t10;
	let current;

	icon0 = new Component$1({
			props: { icon: "logos:svelte-icon", inline: true }
		});

	icon1 = new Component$1({
			props: {
				icon: "logos:supabase-icon",
				inline: true
			}
		});

	icon2 = new Component$1({
			props: {
				color: "white",
				icon: "mdi:github",
				inline: true
			}
		});

	let if_block0 = /*subheading*/ ctx[1].html && create_if_block_5$1(ctx);

	icon3 = new Component$1({
			props: {
				icon: "material-symbols:arrow-forward-rounded"
			}
		});

	let if_block1 = /*videoModalVisible*/ ctx[5] && create_if_block_4$1(ctx);
	let if_block2 = /*modalVisible*/ ctx[4] && create_if_block$2(ctx);

	return {
		c() {
			div6 = element("div");
			div5 = element("div");
			header = element("header");
			div0 = element("div");
			t0 = space();
			div3 = element("div");
			h1 = element("h1");
			t1 = space();
			div1 = element("div");
			t2 = text("Powered by ");
			a0 = element("a");
			create_component(icon0.$$.fragment);
			t3 = text(", ");
			a1 = element("a");
			create_component(icon1.$$.fragment);
			t4 = text(", and ");
			a2 = element("a");
			create_component(icon2.$$.fragment);
			t5 = space();
			if (if_block0) if_block0.c();
			t6 = space();
			div2 = element("div");
			a3 = element("a");
			t7 = text("Get Started\n        ");
			create_component(icon3.$$.fragment);
			t8 = space();
			div4 = element("div");
			figure = element("figure");
			iframe = element("iframe");
			t9 = space();
			if (if_block1) if_block1.c();
			t10 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div6 = claim_element(nodes, "DIV", { class: true, id: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			header = claim_element(div5_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			children(div0).forEach(detach);
			t0 = claim_space(header_nodes);
			div3 = claim_element(header_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			h1 = claim_element(div3_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			h1_nodes.forEach(detach);
			t1 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			t2 = claim_text(div1_nodes, "Powered by ");
			a0 = claim_element(div1_nodes, "A", { href: true, target: true, class: true });
			var a0_nodes = children(a0);
			claim_component(icon0.$$.fragment, a0_nodes);
			a0_nodes.forEach(detach);
			t3 = claim_text(div1_nodes, ", ");
			a1 = claim_element(div1_nodes, "A", { href: true, target: true, class: true });
			var a1_nodes = children(a1);
			claim_component(icon1.$$.fragment, a1_nodes);
			a1_nodes.forEach(detach);
			t4 = claim_text(div1_nodes, ", and ");
			a2 = claim_element(div1_nodes, "A", { href: true, target: true, class: true });
			var a2_nodes = children(a2);
			claim_component(icon2.$$.fragment, a2_nodes);
			a2_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t5 = claim_space(div3_nodes);
			if (if_block0) if_block0.l(div3_nodes);
			t6 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);

			a3 = claim_element(div2_nodes, "A", {
				href: true,
				class: true,
				target: true,
				rel: true
			});

			var a3_nodes = children(a3);
			t7 = claim_text(a3_nodes, "Get Started\n        ");
			claim_component(icon3.$$.fragment, a3_nodes);
			a3_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t8 = claim_space(header_nodes);
			div4 = claim_element(header_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			figure = claim_element(div4_nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);

			iframe = claim_element(figure_nodes, "IFRAME", {
				src: true,
				width: true,
				height: true,
				frameborder: true,
				allow: true,
				title: true,
				class: true
			});

			children(iframe).forEach(detach);
			figure_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t9 = claim_space(div5_nodes);
			if (if_block1) if_block1.l(div5_nodes);
			t10 = claim_space(div5_nodes);
			if (if_block2) if_block2.l(div5_nodes);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "gradient svelte-17457rs");
			attr(h1, "class", "heading svelte-17457rs");
			attr(a0, "href", "https://svelte.dev");
			attr(a0, "target", "blank");
			attr(a0, "class", "svelte-17457rs");
			attr(a1, "href", "https://supabase.com");
			attr(a1, "target", "blank");
			attr(a1, "class", "svelte-17457rs");
			attr(a2, "href", "https://github.com");
			attr(a2, "target", "blank");
			attr(a2, "class", "svelte-17457rs");
			attr(div1, "class", "subheading svelte-17457rs");
			attr(a3, "href", "https://docs.primocms.org/getting-started");
			attr(a3, "class", "button primary svelte-17457rs");
			attr(a3, "target", "_blank");
			attr(a3, "rel", "noreferrer");
			attr(div2, "class", "buttons svelte-17457rs");
			attr(div3, "class", "top svelte-17457rs");
			if (!src_url_equal(iframe.src, iframe_src_value = "https://player.vimeo.com/video/" + /*video_id*/ ctx[2] + "?h=df40df2d2c&badge=0&loop=1&autopause=0&player_id=0&autoplay=1&muted=1&loop=1&title=0&sidedock=0&controls=&app_id=58479")) attr(iframe, "src", iframe_src_value);
			attr(iframe, "width", "2304");
			attr(iframe, "height", "1440");
			attr(iframe, "frameborder", "0");
			attr(iframe, "allow", "autoplay; fullscreen; picture-in-picture");
			iframe.allowFullscreen = true;
			attr(iframe, "title", "Landing Page Demo");
			attr(iframe, "class", "svelte-17457rs");
			attr(figure, "class", "svelte-17457rs");
			attr(div4, "class", "right svelte-17457rs");
			attr(header, "class", "section-container svelte-17457rs");
			attr(div5, "class", "component");
			attr(div6, "class", "section");
			attr(div6, "id", "section-885d7628-0612-43ce-8832-6dce430b0e83");
		},
		m(target, anchor) {
			insert_hydration(target, div6, anchor);
			append_hydration(div6, div5);
			append_hydration(div5, header);
			append_hydration(header, div0);
			append_hydration(header, t0);
			append_hydration(header, div3);
			append_hydration(div3, h1);
			h1.innerHTML = raw_value;
			append_hydration(div3, t1);
			append_hydration(div3, div1);
			append_hydration(div1, t2);
			append_hydration(div1, a0);
			mount_component(icon0, a0, null);
			append_hydration(div1, t3);
			append_hydration(div1, a1);
			mount_component(icon1, a1, null);
			append_hydration(div1, t4);
			append_hydration(div1, a2);
			mount_component(icon2, a2, null);
			append_hydration(div3, t5);
			if (if_block0) if_block0.m(div3, null);
			append_hydration(div3, t6);
			append_hydration(div3, div2);
			append_hydration(div2, a3);
			append_hydration(a3, t7);
			mount_component(icon3, a3, null);
			append_hydration(header, t8);
			append_hydration(header, div4);
			append_hydration(div4, figure);
			append_hydration(figure, iframe);
			append_hydration(div5, t9);
			if (if_block1) if_block1.m(div5, null);
			append_hydration(div5, t10);
			if (if_block2) if_block2.m(div5, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if ((!current || dirty & /*heading*/ 1) && raw_value !== (raw_value = /*heading*/ ctx[0].html + "")) h1.innerHTML = raw_value;
			if (/*subheading*/ ctx[1].html) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_5$1(ctx);
					if_block0.c();
					if_block0.m(div3, t6);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (!current || dirty & /*video_id*/ 4 && !src_url_equal(iframe.src, iframe_src_value = "https://player.vimeo.com/video/" + /*video_id*/ ctx[2] + "?h=df40df2d2c&badge=0&loop=1&autopause=0&player_id=0&autoplay=1&muted=1&loop=1&title=0&sidedock=0&controls=&app_id=58479")) {
				attr(iframe, "src", iframe_src_value);
			}

			if (/*videoModalVisible*/ ctx[5]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty & /*videoModalVisible*/ 32) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block_4$1(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(div5, t10);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}

			if (/*modalVisible*/ ctx[4]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*modalVisible*/ 16) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$2(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div5, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon0.$$.fragment, local);
			transition_in(icon1.$$.fragment, local);
			transition_in(icon2.$$.fragment, local);
			transition_in(icon3.$$.fragment, local);
			transition_in(if_block1);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon0.$$.fragment, local);
			transition_out(icon1.$$.fragment, local);
			transition_out(icon2.$$.fragment, local);
			transition_out(icon3.$$.fragment, local);
			transition_out(if_block1);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div6);
			destroy_component(icon0);
			destroy_component(icon1);
			destroy_component(icon2);
			if (if_block0) if_block0.d();
			destroy_component(icon3);
			if (if_block1) if_block1.d();
			if (if_block2) if_block2.d();
		}
	};
}

let consented = true;

const keyup_handler = () => {
	
};

const keyup_handler_1 = () => {
	
};

const keyup_handler_2 = () => {
	
};

function instance$3($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { footer } = $$props;
	let { video_id } = $$props;
	let { modal } = $$props;
	let { platforms } = $$props;
	let { intro_video_id } = $$props;
	let { svelte_logo } = $$props;

	// import mixpanel from "mixpanel-browser";
	let modalVisible = false;

	let videoModalVisible = false;
	let downloading = false;
	let currentPlatform = getPlatform(window.navigator.platform) || { name: '', disabled: false };

	function getPlatform(platform) {
		if (platform.includes("Win")) {
			return find(platforms, ["name", "Windows"]);
		} else if (platform.includes("Linux")) {
			return find(platforms, ["name", "Linux"]);
		} else {
			return find(platforms, ["name", "Mac (Silicon)"]);
		}
	}

	function hideModal() {
		$$invalidate(6, downloading = false);
		$$invalidate(4, modalVisible = false);
		$$invalidate(5, videoModalVisible = false);
	}

	onMount(() => {
		document.querySelectorAll('a[href="https://svelte.dev"]').forEach(a => {
			a.addEventListener('click', () => {
				mixpanel.track("Reffered to svelte.dev");
			});
		});
	});

	// Safari 3.0+ "[object HTMLElementConstructor]" 
	var isSafari = (/constructor/i).test(window.HTMLElement) || (function (p) {
		return p.toString() === "[object SafariRemoteNotification]";
	})(!window['safari'] || typeof safari !== 'undefined' && window['safari'].pushNotification);

	// Chrome 1 - 79
	var isChrome = !!window.chrome && (!!window.chrome.webstore || !!window.chrome.runtime);

	const click_handler = () => {
		$$invalidate(6, downloading = true);
	};

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(9, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(10, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(11, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('footer' in $$props) $$invalidate(12, footer = $$props.footer);
		if ('video_id' in $$props) $$invalidate(2, video_id = $$props.video_id);
		if ('modal' in $$props) $$invalidate(3, modal = $$props.modal);
		if ('platforms' in $$props) $$invalidate(13, platforms = $$props.platforms);
		if ('intro_video_id' in $$props) $$invalidate(14, intro_video_id = $$props.intro_video_id);
		if ('svelte_logo' in $$props) $$invalidate(15, svelte_logo = $$props.svelte_logo);
	};

	return [
		heading,
		subheading,
		video_id,
		modal,
		modalVisible,
		videoModalVisible,
		downloading,
		currentPlatform,
		hideModal,
		title,
		favicon,
		description,
		footer,
		platforms,
		intro_video_id,
		svelte_logo,
		click_handler
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			title: 9,
			favicon: 10,
			description: 11,
			heading: 0,
			subheading: 1,
			footer: 12,
			video_id: 2,
			modal: 3,
			platforms: 13,
			intro_video_id: 14,
			svelte_logo: 15
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i];
	return child_ctx;
}

// (124:10) {#if teaser.link.label}
function create_if_block_1$3(ctx) {
	let a;
	let t_value = /*teaser*/ ctx[6].link.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-klxdzx");
			attr(a, "href", a_href_value = /*teaser*/ ctx[6].link.url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 4 && t_value !== (t_value = /*teaser*/ ctx[6].link.label + "")) set_data(t, t_value);

			if (dirty & /*teasers*/ 4 && a_href_value !== (a_href_value = /*teaser*/ ctx[6].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (137:10) {:else}
function create_else_block$3(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*teaser*/ ctx[6].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*teaser*/ ctx[6].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 4 && !src_url_equal(img.src, img_src_value = /*teaser*/ ctx[6].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*teasers*/ 4 && img_alt_value !== (img_alt_value = /*teaser*/ ctx[6].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (131:10) {#if teaser.video}
function create_if_block$3(ctx) {
	let iframe;
	let iframe_src_value;

	return {
		c() {
			iframe = element("iframe");
			this.h();
		},
		l(nodes) {
			iframe = claim_element(nodes, "IFRAME", {
				src: true,
				frameborder: true,
				allow: true,
				title: true,
				class: true
			});

			children(iframe).forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(iframe.src, iframe_src_value = "https://player.vimeo.com/video/" + /*teaser*/ ctx[6].video + "?h=c4704a8ede&autoplay=1&muted=1&loop=1&autopause=0")) attr(iframe, "src", iframe_src_value);
			attr(iframe, "frameborder", "0");
			attr(iframe, "allow", "autoplay; fullscreen; picture-in-picture");
			attr(iframe, "title", "video");
			attr(iframe, "class", "svelte-klxdzx");
		},
		m(target, anchor) {
			insert_hydration(target, iframe, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 4 && !src_url_equal(iframe.src, iframe_src_value = "https://player.vimeo.com/video/" + /*teaser*/ ctx[6].video + "?h=c4704a8ede&autoplay=1&muted=1&loop=1&autopause=0")) {
				attr(iframe, "src", iframe_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(iframe);
		}
	};
}

// (119:4) {#each teasers as teaser}
function create_each_block$1(ctx) {
	let div2;
	let div1;
	let h2;
	let t0_value = /*teaser*/ ctx[6].title + "";
	let t0;
	let t1;
	let div0;
	let raw_value = /*teaser*/ ctx[6].body.html + "";
	let t2;
	let t3;
	let figure;
	let t4;
	let if_block0 = /*teaser*/ ctx[6].link.label && create_if_block_1$3(ctx);

	function select_block_type(ctx, dirty) {
		if (/*teaser*/ ctx[6].video) return create_if_block$3;
		return create_else_block$3;
	}

	let current_block_type = select_block_type(ctx);
	let if_block1 = current_block_type(ctx);

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			h2 = element("h2");
			t0 = text(t0_value);
			t1 = space();
			div0 = element("div");
			t2 = space();
			if (if_block0) if_block0.c();
			t3 = space();
			figure = element("figure");
			if_block1.c();
			t4 = space();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, t0_value);
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			if (if_block0) if_block0.l(div1_nodes);
			div1_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			figure = claim_element(div2_nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			if_block1.l(figure_nodes);
			figure_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-klxdzx");
			attr(div0, "class", "body");
			attr(div1, "class", "content svelte-klxdzx");
			attr(figure, "class", "svelte-klxdzx");
			attr(div2, "class", "teaser svelte-klxdzx");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div1, t2);
			if (if_block0) if_block0.m(div1, null);
			append_hydration(div2, t3);
			append_hydration(div2, figure);
			if_block1.m(figure, null);
			append_hydration(div2, t4);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 4 && t0_value !== (t0_value = /*teaser*/ ctx[6].title + "")) set_data(t0, t0_value);
			if (dirty & /*teasers*/ 4 && raw_value !== (raw_value = /*teaser*/ ctx[6].body.html + "")) div0.innerHTML = raw_value;
			if (/*teaser*/ ctx[6].link.label) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_1$3(ctx);
					if_block0.c();
					if_block0.m(div1, null);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if_block1.d(1);
				if_block1 = current_block_type(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(figure, null);
				}
			}
		},
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block0) if_block0.d();
			if_block1.d();
		}
	};
}

function create_fragment$4(ctx) {
	let div2;
	let div1;
	let section;
	let header;
	let h2;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let div0;
	let each_value = /*teasers*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			section = element("section");
			header = element("header");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			h3 = element("h3");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			header = claim_element(section_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			h2 = claim_element(header_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			h3 = claim_element(header_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*subheading*/ ctx[1]);
			h3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-klxdzx");
			attr(h3, "class", "subheading svelte-klxdzx");
			attr(header, "class", "svelte-klxdzx");
			attr(div0, "class", "teasers svelte-klxdzx");
			attr(section, "class", "section-container svelte-klxdzx");
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-ddd59217-6212-4e8b-84ad-036c1b5285d5");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, section);
			append_hydration(section, header);
			append_hydration(header, h2);
			append_hydration(h2, t0);
			append_hydration(header, t1);
			append_hydration(header, h3);
			append_hydration(h3, t2);
			append_hydration(section, t3);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (dirty & /*teasers*/ 4) {
				each_value = /*teasers*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { teasers } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(5, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('teasers' in $$props) $$invalidate(2, teasers = $$props.teasers);
	};

	return [heading, subheading, teasers, title, favicon, description];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			title: 3,
			favicon: 4,
			description: 5,
			heading: 0,
			subheading: 1,
			teasers: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i];
	child_ctx[14] = i;
	return child_ctx;
}

// (176:2) {#if heading}
function create_if_block_2$2(ctx) {
	let header;
	let div;
	let t0;
	let h3;
	let t1;

	return {
		c() {
			header = element("header");
			div = element("div");
			t0 = space();
			h3 = element("h3");
			t1 = text(/*subheading*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			header = claim_element(nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div = claim_element(header_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			div_nodes.forEach(detach);
			t0 = claim_space(header_nodes);
			h3 = claim_element(header_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, /*subheading*/ ctx[1]);
			h3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "heading");
			attr(h3, "class", "subheading");
			attr(header, "class", "svelte-b58jhf");
		},
		m(target, anchor) {
			insert_hydration(target, header, anchor);
			append_hydration(header, div);
			div.innerHTML = /*heading*/ ctx[0];
			append_hydration(header, t0);
			append_hydration(header, h3);
			append_hydration(h3, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*heading*/ 1) div.innerHTML = /*heading*/ ctx[0];			if (dirty & /*subheading*/ 2) set_data(t1, /*subheading*/ ctx[1]);
		},
		d(detaching) {
			if (detaching) detach(header);
		}
	};
}

// (188:10) {:else}
function create_else_block$4(ctx) {
	let html_tag;
	let raw_value = /*item*/ ctx[12].svg + "";
	let html_anchor;

	return {
		c() {
			html_tag = new HtmlTagHydration(false);
			html_anchor = empty();
			this.h();
		},
		l(nodes) {
			html_tag = claim_html_tag(nodes, false);
			html_anchor = empty();
			this.h();
		},
		h() {
			html_tag.a = html_anchor;
		},
		m(target, anchor) {
			html_tag.m(raw_value, target, anchor);
			insert_hydration(target, html_anchor, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 4 && raw_value !== (raw_value = /*item*/ ctx[12].svg + "")) html_tag.p(raw_value);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(html_anchor);
			if (detaching) html_tag.d();
		}
	};
}

// (186:10) {#if item.icon}
function create_if_block_1$4(ctx) {
	let icon;
	let current;
	icon = new Component$1({ props: { icon: /*item*/ ctx[12].icon } });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*items*/ 4) icon_changes.icon = /*item*/ ctx[12].icon;
			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (183:4) {#each items as item, i}
function create_each_block$2(ctx) {
	let li;
	let h3;
	let current_block_type_index;
	let if_block;
	let t0;
	let span;
	let raw0_value = /*item*/ ctx[12].title + "";
	let t1;
	let div;
	let raw1_value = /*item*/ ctx[12].description.html + "";
	let div_data_key_value;
	let t2;
	let current;
	const if_block_creators = [create_if_block_1$4, create_else_block$4];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*item*/ ctx[12].icon) return 0;
		return 1;
	}

	current_block_type_index = select_block_type(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			li = element("li");
			h3 = element("h3");
			if_block.c();
			t0 = space();
			span = element("span");
			t1 = space();
			div = element("div");
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			h3 = claim_element(li_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			if_block.l(h3_nodes);
			t0 = claim_space(h3_nodes);
			span = claim_element(h3_nodes, "SPAN", {});
			var span_nodes = children(span);
			span_nodes.forEach(detach);
			h3_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			div = claim_element(li_nodes, "DIV", { class: true, "data-key": true });
			var div_nodes = children(div);
			div_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "title svelte-b58jhf");
			attr(div, "class", "description svelte-b58jhf");
			attr(div, "data-key", div_data_key_value = "items[" + /*i*/ ctx[14] + "].description");
			attr(li, "class", "svelte-b58jhf");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, h3);
			if_blocks[current_block_type_index].m(h3, null);
			append_hydration(h3, t0);
			append_hydration(h3, span);
			span.innerHTML = raw0_value;
			append_hydration(li, t1);
			append_hydration(li, div);
			div.innerHTML = raw1_value;
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(h3, t0);
			}

			if ((!current || dirty & /*items*/ 4) && raw0_value !== (raw0_value = /*item*/ ctx[12].title + "")) span.innerHTML = raw0_value;			if ((!current || dirty & /*items*/ 4) && raw1_value !== (raw1_value = /*item*/ ctx[12].description.html + "")) div.innerHTML = raw1_value;		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			if_blocks[current_block_type_index].d();
		}
	};
}

// (197:2) {#if link.label}
function create_if_block$4(ctx) {
	let a;
	let span;
	let t0_value = /*link*/ ctx[3].label + "";
	let t0;
	let t1;
	let svg;
	let path;
	let a_href_value;

	return {
		c() {
			a = element("a");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			svg = svg_element("svg");
			path = svg_element("path");
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(a_nodes);

			svg = claim_svg_element(a_nodes, "svg", {
				width: true,
				height: true,
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg_nodes = children(svg);
			path = claim_svg_element(svg_nodes, "path", { d: true, fill: true });
			children(path).forEach(detach);
			svg_nodes.forEach(detach);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-b58jhf");
			attr(path, "d", "M6.81566 0.190662L6.19694 0.809381C6.0505 0.955818 6.0505 1.19326 6.19694 1.33972L11.0448 6.1875H0.375C0.167906 6.1875 0 6.35541 0 6.5625V7.4375C0 7.6446 0.167906 7.8125 0.375 7.8125H11.0448L6.19694 12.6603C6.0505 12.8068 6.0505 13.0442 6.19694 13.1907L6.81566 13.8094C6.96209 13.9558 7.19953 13.9558 7.346 13.8094L13.8902 7.26519C14.0366 7.11875 14.0366 6.88132 13.8902 6.73485L7.34597 0.190662C7.19953 0.0441934 6.96209 0.0441934 6.81566 0.190662Z");
			attr(path, "fill", "currentColor");
			attr(svg, "width", "14");
			attr(svg, "height", "14");
			attr(svg, "viewBox", "0 0 14 14");
			attr(svg, "fill", "none");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg, "class", "svelte-b58jhf");
			attr(a, "class", "arrow-link svelte-b58jhf");
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, span);
			append_hydration(span, t0);
			append_hydration(a, t1);
			append_hydration(a, svg);
			append_hydration(svg, path);
		},
		p(ctx, dirty) {
			if (dirty & /*link*/ 8 && t0_value !== (t0_value = /*link*/ ctx[3].label + "")) set_data(t0, t0_value);

			if (dirty & /*link*/ 8 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$5(ctx) {
	let div1;
	let div0;
	let section;
	let t0;
	let ul;
	let t1;
	let current;
	let if_block0 = /*heading*/ ctx[0] && create_if_block_2$2(ctx);
	let each_value = /*items*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	let if_block1 = /*link*/ ctx[3].label && create_if_block$4(ctx);

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			section = element("section");
			if (if_block0) if_block0.c();
			t0 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			if (if_block1) if_block1.c();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			section = claim_element(div0_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			if (if_block0) if_block0.l(section_nodes);
			t0 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			if (if_block1) if_block1.l(section_nodes);
			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(ul, "class", "svelte-b58jhf");
			attr(section, "class", "section-container svelte-b58jhf");
			attr(div0, "class", "component");
			attr(div1, "class", "section");
			attr(div1, "id", "section-d294b81b-78a4-4285-8347-c9d078edaec9");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, section);
			if (if_block0) if_block0.m(section, null);
			append_hydration(section, t0);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(section, t1);
			if (if_block1) if_block1.m(section, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if (/*heading*/ ctx[0]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_2$2(ctx);
					if_block0.c();
					if_block0.m(section, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (dirty & /*items*/ 4) {
				each_value = /*items*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (/*link*/ ctx[3].label) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block$4(ctx);
					if_block1.c();
					if_block1.m(section, null);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			if (if_block0) if_block0.d();
			destroy_each(each_blocks, detaching);
			if (if_block1) if_block1.d();
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { items } = $$props;
	let { link } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(6, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('items' in $$props) $$invalidate(2, items = $$props.items);
		if ('link' in $$props) $$invalidate(3, link = $$props.link);
	};

	return [heading, subheading, items, link, title, favicon, description];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			title: 4,
			favicon: 5,
			description: 6,
			heading: 0,
			subheading: 1,
			items: 2,
			link: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
	let div15;
	let div14;
	let section;
	let div13;
	let div0;
	let h2;
	let t0_value = /*signup_form*/ ctx[0].heading + "";
	let t0;
	let t1;
	let h3;
	let raw_value = /*signup_form*/ ctx[0].subheading.html + "";
	let t2;
	let div12;
	let div11;
	let div10;
	let div9;
	let div6;
	let form;
	let div3;
	let div2;
	let div1;
	let input0;
	let t3;
	let input1;
	let t4;
	let div5;
	let button0;
	let t5;
	let t6;
	let button1;
	let div4;
	let t7;
	let span;
	let t8;
	let t9;
	let input2;
	let t10;
	let div8;
	let div7;
	let h4;
	let t11;
	let t12;
	let p;
	let t13;
	let t14;
	let img;
	let img_src_value;
	let t15;
	let script0;
	let t16;
	let t17;
	let script1;
	let script1_src_value;
	let t18;
	let link;

	return {
		c() {
			div15 = element("div");
			div14 = element("div");
			section = element("section");
			div13 = element("div");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(t0_value);
			t1 = space();
			h3 = element("h3");
			t2 = space();
			div12 = element("div");
			div11 = element("div");
			div10 = element("div");
			div9 = element("div");
			div6 = element("div");
			form = element("form");
			div3 = element("div");
			div2 = element("div");
			div1 = element("div");
			input0 = element("input");
			t3 = space();
			input1 = element("input");
			t4 = space();
			div5 = element("div");
			button0 = element("button");
			t5 = text("Subscribe");
			t6 = space();
			button1 = element("button");
			div4 = element("div");
			t7 = space();
			span = element("span");
			t8 = text("Loading...");
			t9 = space();
			input2 = element("input");
			t10 = space();
			div8 = element("div");
			div7 = element("div");
			h4 = element("h4");
			t11 = text("Thank you!");
			t12 = space();
			p = element("p");
			t13 = text("You have successfully joined our subscriber list.");
			t14 = space();
			img = element("img");
			t15 = space();
			script0 = element("script");
			t16 = text("function ml_webform_success_5039306() {\n      var r = ml_jQuery || jQuery;\n      r(\".ml-subscribe-form-5039306 .row-success\").show(),\n        r(\".ml-subscribe-form-5039306 .row-form\").hide();\n    }");
			t17 = space();
			script1 = element("script");
			t18 = space();
			link = element("link");
			this.h();
		},
		l(nodes) {
			div15 = claim_element(nodes, "DIV", { class: true, id: true });
			var div15_nodes = children(div15);
			div14 = claim_element(div15_nodes, "DIV", { class: true });
			var div14_nodes = children(div14);
			section = claim_element(div14_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div13 = claim_element(section_nodes, "DIV", { class: true });
			var div13_nodes = children(div13);
			div0 = claim_element(div13_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, t0_value);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			h3_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t2 = claim_space(div13_nodes);
			div12 = claim_element(div13_nodes, "DIV", { class: true });
			var div12_nodes = children(div12);
			div11 = claim_element(div12_nodes, "DIV", { id: true, class: true });
			var div11_nodes = children(div11);
			div10 = claim_element(div11_nodes, "DIV", { class: true });
			var div10_nodes = children(div10);
			div9 = claim_element(div10_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			div6 = claim_element(div9_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);

			form = claim_element(div6_nodes, "FORM", {
				class: true,
				action: true,
				"data-code": true,
				method: true,
				target: true
			});

			var form_nodes = children(form);
			div3 = claim_element(form_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			input0 = claim_element(div1_nodes, "INPUT", {
				"aria-label": true,
				"aria-required": true,
				type: true,
				class: true,
				"data-inputmask": true,
				name: true,
				placeholder: true,
				autocomplete: true
			});

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t3 = claim_space(form_nodes);
			input1 = claim_element(form_nodes, "INPUT", { type: true, name: true, class: true });
			t4 = claim_space(form_nodes);
			div5 = claim_element(form_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			button0 = claim_element(div5_nodes, "BUTTON", { type: true, class: true });
			var button0_nodes = children(button0);
			t5 = claim_text(button0_nodes, "Subscribe");
			button0_nodes.forEach(detach);
			t6 = claim_space(div5_nodes);
			button1 = claim_element(div5_nodes, "BUTTON", { style: true, type: true, class: true });
			var button1_nodes = children(button1);
			div4 = claim_element(button1_nodes, "DIV", { class: true });
			children(div4).forEach(detach);
			t7 = claim_space(button1_nodes);
			span = claim_element(button1_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t8 = claim_text(span_nodes, "Loading...");
			span_nodes.forEach(detach);
			button1_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			t9 = claim_space(form_nodes);
			input2 = claim_element(form_nodes, "INPUT", { type: true, name: true, class: true });
			form_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			t10 = claim_space(div9_nodes);
			div8 = claim_element(div9_nodes, "DIV", { class: true, style: true });
			var div8_nodes = children(div8);
			div7 = claim_element(div8_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			h4 = claim_element(div7_nodes, "H4", {});
			var h4_nodes = children(h4);
			t11 = claim_text(h4_nodes, "Thank you!");
			h4_nodes.forEach(detach);
			t12 = claim_space(div7_nodes);
			p = claim_element(div7_nodes, "P", {});
			var p_nodes = children(p);
			t13 = claim_text(p_nodes, "You have successfully joined our subscriber list.");
			p_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			div11_nodes.forEach(detach);
			t14 = claim_space(div12_nodes);

			img = claim_element(div12_nodes, "IMG", {
				src: true,
				width: true,
				height: true,
				style: true,
				alt: true,
				border: true
			});

			div12_nodes.forEach(detach);
			t15 = claim_space(div13_nodes);
			script0 = claim_element(div13_nodes, "SCRIPT", {});
			var script0_nodes = children(script0);
			t16 = claim_text(script0_nodes, "function ml_webform_success_5039306() {\n      var r = ml_jQuery || jQuery;\n      r(\".ml-subscribe-form-5039306 .row-success\").show(),\n        r(\".ml-subscribe-form-5039306 .row-form\").hide();\n    }");
			script0_nodes.forEach(detach);
			t17 = claim_space(div13_nodes);
			script1 = claim_element(div13_nodes, "SCRIPT", { src: true, type: true });
			var script1_nodes = children(script1);
			script1_nodes.forEach(detach);
			div13_nodes.forEach(detach);
			section_nodes.forEach(detach);
			t18 = claim_space(div14_nodes);

			link = claim_element(div14_nodes, "LINK", {
				rel: true,
				href: true,
				integrity: true,
				crossorigin: true,
				referrerpolicy: true
			});

			div14_nodes.forEach(detach);
			div15_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-l19rlb");
			attr(h3, "class", "subheading content svelte-l19rlb");
			attr(div0, "class", "inner-content svelte-l19rlb");
			attr(input0, "aria-label", "email");
			attr(input0, "aria-required", "true");
			attr(input0, "type", "email");
			attr(input0, "class", "form-control svelte-l19rlb");
			attr(input0, "data-inputmask", "");
			attr(input0, "name", "fields[email]");
			attr(input0, "placeholder", "Email");
			attr(input0, "autocomplete", "email");
			attr(div1, "class", "ml-field-group ml-field-email ml-validate-email ml-validate-required");
			attr(div2, "class", "ml-form-fieldRow ml-last-item");
			attr(div3, "class", "ml-form-formContent");
			attr(input1, "type", "hidden");
			attr(input1, "name", "ml-submit");
			input1.value = "1";
			attr(input1, "class", "svelte-l19rlb");
			attr(button0, "type", "submit");
			attr(button0, "class", "button primary svelte-l19rlb");
			attr(div4, "class", "ml-form-embedSubmitLoad");
			attr(span, "class", "sr-only");
			button1.disabled = "disabled";
			set_style(button1, "display", "none");
			attr(button1, "type", "button");
			attr(button1, "class", "loading");
			attr(div5, "class", "ml-form-embedSubmit");
			attr(input2, "type", "hidden");
			attr(input2, "name", "anticsrf");
			input2.value = "true";
			attr(input2, "class", "svelte-l19rlb");
			attr(form, "class", "ml-block-form svelte-l19rlb");
			attr(form, "action", "https://static.mailerlite.com/webforms/submit/j2m2z7");
			attr(form, "data-code", "j2m2z7");
			attr(form, "method", "post");
			attr(form, "target", "_blank");
			attr(div6, "class", "ml-form-embedBody ml-form-embedBodyDefault row-form");
			attr(div7, "class", "ml-form-successContent");
			attr(div8, "class", "ml-form-successBody row-success");
			set_style(div8, "display", "none");
			attr(div9, "class", "ml-form-embedWrapper embedForm");
			attr(div10, "class", "ml-form-align-center");
			attr(div11, "id", "mlb2-5039306");
			attr(div11, "class", "ml-form-embedContainer ml-subscribe-form ml-subscribe-form-5039306");
			if (!src_url_equal(img.src, img_src_value = "https://track.mailerlite.com/webforms/o/5039306/j2m2z7?v1637419080")) attr(img, "src", img_src_value);
			attr(img, "width", "1");
			attr(img, "height", "1");
			set_style(img, "max-width", "1px");
			set_style(img, "max-height", "1px");
			set_style(img, "visibility", "hidden");
			set_style(img, "padding", "0");
			set_style(img, "margin", "0");
			set_style(img, "display", "block");
			attr(img, "alt", ".");
			attr(img, "border", "0");
			attr(div12, "class", "form");
			if (!src_url_equal(script1.src, script1_src_value = "https://static.mailerlite.com/js/w/webforms.min.js?v0c75f831c56857441820dcec3163967c")) attr(script1, "src", script1_src_value);
			attr(script1, "type", "text/javascript");
			attr(div13, "class", "section-container svelte-l19rlb");
			attr(section, "class", "svelte-l19rlb");
			attr(link, "rel", "stylesheet");
			attr(link, "href", "https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.0.0-beta2/css/all.min.css");
			attr(link, "integrity", "sha512-YWzhKL2whUzgiheMoBFwW8CKV4qpHQAEuvilg9FAn5VJUDwKZZxkJNuGM4XkWuk94WCrrwslk8yWNGmY1EduTA==");
			attr(link, "crossorigin", "anonymous");
			attr(link, "referrerpolicy", "no-referrer");
			attr(div14, "class", "component");
			attr(div15, "class", "section");
			attr(div15, "id", "section-b18b744b-92ba-4bf9-96fd-4d86c0a842b8");
		},
		m(target, anchor) {
			insert_hydration(target, div15, anchor);
			append_hydration(div15, div14);
			append_hydration(div14, section);
			append_hydration(section, div13);
			append_hydration(div13, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h3);
			h3.innerHTML = raw_value;
			append_hydration(div13, t2);
			append_hydration(div13, div12);
			append_hydration(div12, div11);
			append_hydration(div11, div10);
			append_hydration(div10, div9);
			append_hydration(div9, div6);
			append_hydration(div6, form);
			append_hydration(form, div3);
			append_hydration(div3, div2);
			append_hydration(div2, div1);
			append_hydration(div1, input0);
			append_hydration(form, t3);
			append_hydration(form, input1);
			append_hydration(form, t4);
			append_hydration(form, div5);
			append_hydration(div5, button0);
			append_hydration(button0, t5);
			append_hydration(div5, t6);
			append_hydration(div5, button1);
			append_hydration(button1, div4);
			append_hydration(button1, t7);
			append_hydration(button1, span);
			append_hydration(span, t8);
			append_hydration(form, t9);
			append_hydration(form, input2);
			append_hydration(div9, t10);
			append_hydration(div9, div8);
			append_hydration(div8, div7);
			append_hydration(div7, h4);
			append_hydration(h4, t11);
			append_hydration(div7, t12);
			append_hydration(div7, p);
			append_hydration(p, t13);
			append_hydration(div12, t14);
			append_hydration(div12, img);
			append_hydration(div13, t15);
			append_hydration(div13, script0);
			append_hydration(script0, t16);
			append_hydration(div13, t17);
			append_hydration(div13, script1);
			append_hydration(div14, t18);
			append_hydration(div14, link);
		},
		p(ctx, [dirty]) {
			if (dirty & /*signup_form*/ 1 && t0_value !== (t0_value = /*signup_form*/ ctx[0].heading + "")) set_data(t0, t0_value);
			if (dirty & /*signup_form*/ 1 && raw_value !== (raw_value = /*signup_form*/ ctx[0].subheading.html + "")) h3.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div15);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { signup_form } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(3, description = $$props.description);
		if ('signup_form' in $$props) $$invalidate(0, signup_form = $$props.signup_form);
	};

	return [signup_form, title, favicon, description];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			title: 1,
			favicon: 2,
			description: 3,
			signup_form: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	child_ctx[9] = list[i].icon;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (109:8) {#each footer_nav as { link }}
function create_each_block_1$1(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "class", "svelte-13um1f6");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_nav*/ 1 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*footer_nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (120:6) {#each social as { link, icon }}
function create_each_block$3(ctx) {
	let li;
	let a;
	let icon;
	let a_href_value;
	let a_aria_label_value;
	let t;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[9] } });

	return {
		c() {
			li = element("li");
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);

			a = claim_element(li_nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			a_nodes.forEach(detach);
			t = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "aria-label", a_aria_label_value = /*link*/ ctx[8].label);
			attr(a, "class", "svelte-13um1f6");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			mount_component(icon, a, null);
			append_hydration(li, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 2) icon_changes.icon = /*icon*/ ctx[9];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social*/ 2 && a_aria_label_value !== (a_aria_label_value = /*link*/ ctx[8].label)) {
				attr(a, "aria-label", a_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$7(ctx) {
	let div3;
	let div2;
	let footer;
	let div1;
	let div0;
	let span;
	let t0;
	let a;
	let t1;
	let t2;
	let nav;
	let t3;
	let ul;
	let current;
	let each_value_1 = /*footer_nav*/ ctx[0];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	let each_value = /*social*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$3(get_each_context$3(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			footer = element("footer");
			div1 = element("div");
			div0 = element("div");
			span = element("span");
			t0 = text("Sponsored by ");
			a = element("a");
			t1 = text("Breezly");
			t2 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t3 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			footer = claim_element(div2_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div1 = claim_element(footer_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span = claim_element(div0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, "Sponsored by ");
			a = claim_element(span_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, "Breezly");
			a_nodes.forEach(detach);
			span_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", "https://breezly.io");
			attr(a, "class", "svelte-13um1f6");
			attr(span, "class", "breezly svelte-13um1f6");
			attr(nav, "class", "svelte-13um1f6");
			attr(div0, "class", "container svelte-13um1f6");
			attr(ul, "class", "svelte-13um1f6");
			attr(div1, "class", "section-container svelte-13um1f6");
			attr(footer, "class", "svelte-13um1f6");
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-48a7ea62-7557-43b8-bf58-34e02c928c5e");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, footer);
			append_hydration(footer, div1);
			append_hydration(div1, div0);
			append_hydration(div0, span);
			append_hydration(span, t0);
			append_hydration(span, a);
			append_hydration(a, t1);
			append_hydration(div0, t2);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav, null);
				}
			}

			append_hydration(div1, t3);
			append_hydration(div1, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (dirty & /*footer_nav*/ 1) {
				each_value_1 = /*footer_nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1$1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*social*/ 2) {
				each_value = /*social*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$3(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$3(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { footer_nav } = $$props;
	let { social } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('footer_nav' in $$props) $$invalidate(0, footer_nav = $$props.footer_nav);
		if ('social' in $$props) $$invalidate(1, social = $$props.social);
	};

	return [footer_nav, social, title, favicon, description];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			title: 2,
			favicon: 3,
			description: 4,
			footer_nav: 0,
			social: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function instance$8($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(1, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
	};

	return [title, favicon, description];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$8, null, safe_not_equal, { title: 0, favicon: 1, description: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$8(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let current;

	component_0 = new Component({
			props: {
				title: "Primo",
				favicon: {
					"alt": "",
					"src": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"size": 8
				},
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time."
			}
		});

	component_1 = new Component$2({
			props: {
				title: "Primo",
				favicon: {
					"alt": "",
					"src": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"size": 8
				},
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time.",
				banner: {
					"cta": { "url": "", "label": "", "active": false },
					"label": ""
				},
				logo: {
					"svg": "<svg viewBox=\"0 0 871 198\" fill=\"none\" xmlns=\"http://www.w3.org/2000/svg\"> <g clip-path=\"url(#clip0_250_527)\"> <path d=\"M814.062 159.924C782.686 159.924 757.171 134.408 757.171 103.032C757.171 71.6567 782.686 46.1408 814.062 46.1408C845.438 46.1408 870.954 71.6567 870.954 103.032C870.954 134.408 845.438 159.924 814.062 159.924ZM814.062 70.3186C796.021 70.3186 781.395 84.9914 781.395 102.986C781.395 120.981 796.067 135.654 814.062 135.654C832.057 135.654 846.73 120.981 846.73 102.986C846.73 84.9914 832.057 70.3186 814.062 70.3186Z\" fill=\"#FDFDFD\"/> <path d=\"M700.925 46.0947C689.897 46.0947 679.931 50.5242 672.641 57.676C665.35 50.5242 655.384 46.0947 644.356 46.0947C622.07 46.0947 603.983 64.228 603.983 86.4679V147.789C603.983 154.479 609.382 159.878 616.072 159.878C622.763 159.878 628.161 154.479 628.161 147.789V86.4679C628.161 77.5627 635.405 70.3186 644.31 70.3186C653.215 70.3186 660.46 77.5627 660.46 86.4679V147.789C660.46 154.479 665.858 159.878 672.548 159.878C679.239 159.878 684.637 154.479 684.637 147.789V86.4679C684.637 77.5627 691.881 70.3186 700.787 70.3186C709.692 70.3186 716.936 77.5627 716.936 86.4679V147.789C716.936 154.479 722.334 159.878 729.025 159.878C735.715 159.878 741.114 154.479 741.114 147.789V86.4679C741.114 64.1819 722.98 46.0947 700.74 46.0947H700.925Z\" fill=\"#FDFDFD\"/> <path d=\"M571.039 159.786C564.348 159.786 558.95 154.387 558.95 147.697V58.0913C558.95 51.4009 564.348 46.0024 571.039 46.0024C577.729 46.0024 583.128 51.4009 583.128 58.0913V147.697C583.128 154.387 577.729 159.786 571.039 159.786Z\" fill=\"#FDFDFD\"/> <path d=\"M571.039 26.4848C578.352 26.4848 584.281 20.556 584.281 13.2424C584.281 5.92883 578.352 0 571.039 0C563.725 0 557.796 5.92883 557.796 13.2424C557.796 20.556 563.725 26.4848 571.039 26.4848Z\" fill=\"#FDFDFD\"/> <path d=\"M482.356 159.785C475.666 159.785 470.267 154.387 470.267 147.697V102.894C470.267 71.5181 495.783 46.0023 527.159 46.0023C533.849 46.0023 539.248 51.4007 539.248 58.0911C539.248 64.7816 533.849 70.18 527.159 70.18C509.118 70.18 494.491 84.8528 494.491 102.848V147.65C494.491 154.341 489.093 159.739 482.402 159.739L482.356 159.785Z\" fill=\"#FDFDFD\"/> <path d=\"M349.701 197.99C343.011 197.99 337.612 192.592 337.612 185.901V102.894C337.612 71.5182 363.128 46.0024 394.504 46.0024C425.88 46.0024 451.396 71.5182 451.396 102.894C451.396 134.27 425.88 159.786 394.504 159.786C387.814 159.786 382.415 154.387 382.415 147.697C382.415 141.006 387.814 135.608 394.504 135.608C412.545 135.608 427.172 120.935 427.172 102.94C427.172 84.9452 412.499 70.2724 394.504 70.2724C376.509 70.2724 361.836 84.9452 361.836 102.94V185.947C361.836 192.638 356.438 198.036 349.747 198.036L349.701 197.99Z\" fill=\"#FDFDFD\"/> <path d=\"M222.814 159.371C219.723 159.371 216.631 158.171 214.232 155.818C209.526 151.065 209.526 143.406 214.232 138.699L249.668 103.263L214.232 67.8271C209.526 63.0746 209.526 55.4153 214.232 50.7089C218.984 45.9564 226.644 45.9564 231.35 50.7089L275.368 94.7272C280.075 99.4797 280.075 107.139 275.368 111.845L231.35 155.864C228.997 158.217 225.906 159.417 222.768 159.417L222.814 159.371Z\" fill=\"#35D994\"/> <path d=\"M94.7272 197.99C91.6358 197.99 88.5443 196.791 86.145 194.437L3.55296 111.799C-1.1534 107.047 -1.1534 99.3874 3.55296 94.681L47.5713 50.6627C52.3238 45.9102 59.9832 45.9102 64.6895 50.6627C69.3959 55.4152 69.3959 63.0746 64.6895 67.7809L29.2073 103.217L103.263 177.273C107.97 182.026 107.97 189.685 103.263 194.391C100.91 196.744 97.8186 197.944 94.6811 197.944L94.7272 197.99Z\" fill=\"url(#paint0_linear_250_527)\"/> <path d=\"M94.7273 197.99C88.0369 197.99 82.6384 192.592 82.6384 185.901V102.894C82.6384 71.5181 108.154 46.0023 139.53 46.0023C170.906 46.0023 196.422 71.5181 196.422 102.894C196.422 134.27 170.906 159.785 139.53 159.785C132.84 159.785 127.441 154.387 127.441 147.697C127.441 141.006 132.84 135.608 139.53 135.608C157.571 135.608 172.198 120.935 172.198 102.94C172.198 84.9451 157.525 70.2723 139.53 70.2723C121.535 70.2723 106.862 84.9451 106.862 102.94V185.947C106.862 192.638 101.464 198.036 94.7735 198.036L94.7273 197.99Z\" fill=\"#35D994\"/> </g> <defs> <linearGradient id=\"paint0_linear_250_527\" x1=\"25.5621\" y1=\"72.6719\" x2=\"125.319\" y2=\"172.428\" gradientUnits=\"userSpaceOnUse\"> <stop stop-color=\"#35D994\"/> <stop offset=\"0.16\" stop-color=\"#32D28E\"/> <stop offset=\"0.38\" stop-color=\"#29BF80\"/> <stop offset=\"0.64\" stop-color=\"#1CA169\"/> <stop offset=\"0.93\" stop-color=\"#097649\"/> <stop offset=\"0.95\" stop-color=\"#097548\"/> </linearGradient> <clipPath id=\"clip0_250_527\"> <rect width=\"871\" height=\"197.99\" fill=\"white\"/> </clipPath> </defs> </svg>",
					"title": "primo"
				},
				nav: [
					{
						"link": {
							"url": "https://docs.primocms.org",
							"label": "Docs",
							"active": false
						},
						"links": []
					},
					{
						"link": {
							"url": "/themes",
							"label": "Themes",
							"active": false
						},
						"links": []
					},
					{
						"link": {
							"url": "/primo-cloud-waitlist",
							"label": "Cloud"
						},
						"links": []
					}
				]
			}
		});

	component_2 = new Component$3({
			props: {
				title: "Primo",
				favicon: {
					"alt": "",
					"src": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"size": 8
				},
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time.",
				heading: {
					"html": "<p>Primo is a visual CMS that makes it a blast to build <strong>pages</strong>, manage <strong>content</strong>, and edit <strong>code</strong> - one block at a time.</p>",
					"markdown": "Primo is a visual CMS that makes it a blast to build **pages**, manage **content**, and edit **code** \\- one block at a time.\n\n"
				},
				subheading: { "html": "", "markdown": "" },
				footer: "Esse veniam nulla",
				video_id: "820725171",
				modal: {
					"title": "Cillum qui culpa",
					"content": {
						"html": "<h1 id=\"thisissomemarkdown\">This is some markdown</h1>",
						"markdown": "# This is some markdown"
					},
					"checkbox": "Reprehenderit voluptate veniam",
					"sub_content": "Nostrud ea occaecat",
					"downloading_content": {
						"html": "<h1 id=\"thisissomemarkdown\">This is some markdown</h1>",
						"markdown": "# This is some markdown"
					},
					"sub_content_expanded": {
						"html": "<h1 id=\"thisissomemarkdown\">This is some markdown</h1>",
						"markdown": "# This is some markdown"
					}
				},
				platforms: [
					{
						"svg": "Sint dolore eu",
						"name": "Excepteur in pariatur",
						"disabled": "",
						"description": {
							"html": "<h1 id=\"thisissomemarkdown\">This is some markdown</h1>",
							"markdown": "# This is some markdown"
						},
						"download_link": "Voluptate dolor elit"
					},
					{
						"svg": "Non dolor sunt",
						"name": "Qui magna proident",
						"disabled": "",
						"description": {
							"html": "<h1 id=\"thisissomemarkdown\">This is some markdown</h1>",
							"markdown": "# This is some markdown"
						},
						"download_link": "Dolore irure esse"
					}
				],
				intro_video_id: "Est laboris velit",
				svelte_logo: {
					"alt": "",
					"src": "https://picsum.photos/600/400?blur=10",
					"url": "https://picsum.photos/600/400?blur=10",
					"size": null
				}
			}
		});

	component_3 = new Component$4({
			props: {
				title: "Primo",
				favicon: {
					"alt": "",
					"src": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"size": 8
				},
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time.",
				heading: "The modern monolithic CMS",
				subheading: "Primo combines delightful content management with the power of modern development",
				teasers: [
					{
						"body": {
							"html": "<p>Build your site's pages by dragging and dropping your directly blocks onto the page, unencumbered by overwhelming design options.</p>",
							"markdown": "Build your site's pages by dragging and dropping your directly blocks onto the page, unencumbered by overwhelming design options.\n\n"
						},
						"link": { "url": "/", "label": "", "active": false },
						"image": {
							"alt": "",
							"src": "https://kdtzsoeklezpgshpzqtf.supabase.co/storage/v1/object/public/images/7c1dc1a3-c9eb-4364-b31b-951ecfc2641d/1682111950401Screen%20Shot%202023-04-21%20at%205.17.27%20PM.png",
							"url": "https://kdtzsoeklezpgshpzqtf.supabase.co/storage/v1/object/public/images/7c1dc1a3-c9eb-4364-b31b-951ecfc2641d/1682111950401Screen%20Shot%202023-04-21%20at%205.17.27%20PM.png",
							"size": 251
						},
						"title": "Drag-n-drop page building",
						"video": ""
					},
					{
						"body": {
							"html": "<p>Update your text, images, and links directly on the page or open up the Fields view to manage your content from a structured view.</p>",
							"markdown": "Update your text, images, and links directly on the page or open up the Fields view to manage your content from a structured view.\n\n"
						},
						"link": { "url": "", "label": "", "active": false },
						"image": {
							"alt": "",
							"url": "https://kdtzsoeklezpgshpzqtf.supabase.co/storage/v1/object/public/images/7c1dc1a3-c9eb-4364-b31b-951ecfc2641d/Screen%20Shot%202023-04-21%20at%205.22.39%20PM.png1682112222228"
						},
						"title": "Visual content editing",
						"video": ""
					},
					{
						"body": {
							"html": "<p>Access each block's code with a click - right from your browser. And since each block is a <a href=\"https://svelte.dev\">Svelte</a> component, there's no limit to what you can make.</p>",
							"markdown": "Access each block's code with a click - right from your browser. And since each block is a [Svelte](https://svelte.dev) component, there's no limit to what you can make.\n"
						},
						"link": { "url": "", "label": "", "active": false },
						"image": {
							"alt": "",
							"url": "https://kdtzsoeklezpgshpzqtf.supabase.co/storage/v1/object/public/images/7c1dc1a3-c9eb-4364-b31b-951ecfc2641d/Screen%20Shot%202023-04-21%20at%205.25.06%20PM.png1682112330379"
						},
						"title": "Integrated development",
						"video": ""
					}
				]
			}
		});

	component_4 = new Component$5({
			props: {
				title: "Primo",
				favicon: {
					"alt": "",
					"src": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"size": 8
				},
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time.",
				heading: "",
				subheading: "\n",
				items: [
					{
						"icon": "ph:files-fill",
						"image": {
							"alt": "",
							"src": "https://picsum.photos/600/400?blur=10",
							"url": "https://picsum.photos/600/400?blur=10",
							"size": null
						},
						"title": "Static Sites",
						"description": {
							"html": "<p>Your websites are secure, scalable to millions, and fast-loading - no fancy plugins necessary.</p>",
							"markdown": "Your websites are secure, scalable to millions, and fast-loading - no fancy plugins necessary."
						}
					},
					{
						"icon": "mdi:users-group",
						"image": {
							"alt": "",
							"src": "https://picsum.photos/600/400?blur=10",
							"url": "https://picsum.photos/600/400?blur=10",
							"size": null
						},
						"title": "Real-time collaboration",
						"description": {
							"html": "<p>Invite any number of collaborators as developers or content editors and edit your pages together. </p>",
							"markdown": "Invite any number of collaborators as developers or content editors and edit your pages together. "
						}
					},
					{
						"icon": "fluent-mdl2:locale-language",
						"image": {
							"alt": "",
							"src": "https://picsum.photos/600/400?blur=10",
							"url": "https://picsum.photos/600/400?blur=10",
							"size": null
						},
						"title": "Internationalization",
						"description": {
							"html": "<p>Easily manage content for over 60 locales and build each as a static version so you can rule your SEO.</p>",
							"markdown": "Easily manage content for over 60 locales and build each as a static version so you can rule your SEO."
						}
					},
					{
						"icon": "gg:website",
						"image": {
							"alt": "",
							"src": "https://picsum.photos/600/400?blur=10",
							"url": "https://picsum.photos/600/400?blur=10",
							"size": null
						},
						"title": "Multisite to the max",
						"description": {
							"html": "<h1>Create an unlimited number of websites on a single server and start new sites in seconds.</h1>",
							"markdown": "# Create an unlimited number of websites on a single server and start new sites in seconds.\n\n"
						}
					},
					{
						"icon": "clarity:blocks-group-solid",
						"image": {
							"alt": "",
							"src": "https://picsum.photos/600/400?blur=10",
							"url": "https://picsum.photos/600/400?blur=10",
							"size": null
						},
						"title": "Themes & blocks",
						"description": {
							"html": "<p>Hit the ground running with Primo's free themes and blocks that can be used on any Primo site.</p>",
							"markdown": "Hit the ground running with Primo's free themes and blocks that can be used on any Primo site.\n\n"
						}
					},
					{
						"icon": "mdi:github",
						"image": {
							"alt": "",
							"src": "https://picsum.photos/600/400?blur=10",
							"url": "https://picsum.photos/600/400?blur=10",
							"size": null
						},
						"title": "Deploy to Github",
						"description": {
							"html": "<h1 id=\"deployyoursitetoagithubrepositoryfromwhereyoucaneasilydeployittoanywebhost\">Deploy your site to a Github repository, from where you can easily deploy it to any web host.</h1>",
							"markdown": "# Deploy your site to a Github repository, from where you can easily deploy it to any web host.\n\n"
						}
					}
				],
				link: { "url": "/", "label": "" }
			}
		});

	component_5 = new Component$6({
			props: {
				title: "Primo",
				favicon: {
					"alt": "",
					"src": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"size": 8
				},
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time.",
				signup_form: {
					"heading": "Hear about future updates, including:",
					"subheading": {
						"html": "<ul><li><p><strong>Using it headless</strong> alongside SvelteKit, NextJS, etc.</p></li><li><p><strong>Leveraging GPT4</strong> to create unique sites, pages, and blocks with a prompt.</p></li><li><p><strong>Design fields</strong> to give content editors style options.</p></li><li><p><strong>Cloud functions</strong> for writing backend code from Primo.</p></li></ul>",
						"markdown": "- **Using it headless** alongside SvelteKit, NextJS, etc.\n\n- **Leveraging GPT4** to create unique sites, pages, and blocks with a prompt.\n\n- **Design fields** to give content editors style options.\n\n- **Cloud functions** for writing backend code from Primo.\n\n\n<!-- -->\n\n"
					}
				}
			}
		});

	component_6 = new Component$7({
			props: {
				title: "Primo",
				favicon: {
					"alt": "",
					"src": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"size": 8
				},
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time.",
				footer_nav: [
					{
						"link": { "url": "/", "label": "Changelog" }
					},
					{
						"link": { "url": "/", "label": "Open Source" }
					},
					{
						"link": { "url": "/", "label": "Terms of Service" }
					}
				],
				social: [
					{
						"icon": "fa6-brands:discourse",
						"link": {
							"url": "https://forum.primo.so",
							"label": "Forum"
						}
					},
					{
						"icon": "fa6-brands:discord",
						"link": {
							"url": "https://discord.gg/DMQshmek8m",
							"label": "Discord"
						}
					},
					{
						"icon": "fa6-brands:youtube",
						"link": {
							"url": "https://www.youtube.com/@primocms",
							"label": "Youtube"
						}
					},
					{
						"icon": "fa6-brands:github",
						"link": {
							"url": "https://github.com/primocms/primo",
							"label": "Github"
						}
					}
				]
			}
		});

	component_7 = new Component$8({
			props: {
				title: "Primo",
				favicon: {
					"alt": "",
					"src": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"url": "https://dbfnrqvkgwkjkzqgnfrd.supabase.co/storage/v1/object/public/images/1a9f29e7-b37e-4a46-adcf-49d3b854ed8a/1680814436263_p_%20Mark%20in%20App%20Icon.png",
					"size": 8
				},
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time."
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
		}
	};
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$8, safe_not_equal, {});
	}
}

export default Component$9;
