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

/* generated by Svelte v3.59.1 */

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
			t = text("@import url(\"https://unpkg.com/tailwindcss@2.2.15/dist/base.css\");\n@import url(https://fonts.bunny.net/css?family=archivo:200,300,300i,400,400i,500,500i,600,600i,700,700i);\n\n#page {\n  --color-primored: #35d994;\n  --color-gray: #262626;\n  --color-black: #121212;\n  --color-white: #ffff;\n  --color-accent: var(--color-primored);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.1);\n\n  --padding-left: 2rem;\n  --padding-right: 2rem;\n\n  --color: #F3F3F3;\n  --background: var(--color-black);\n  --max-width: 1000px;\n  --border-color: var(--color-gray);\n  --border: 2px solid var(--border-color);\n  --border-radius: 5px;\n\n  --heading-font-size: clamp(1rem, 10vw, 2.25rem);\n  --heading-color: #FDFDFD;\n  --heading-font-weight: 600;\n  --heading-line-height: 1.3;\n  --subheading-color: #DADADA;\n  --body-color: #CECECE;\n  --heading-line-height: 1.3;\n\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color, var(--transition-time) background,\n    var(--transition-time) border-color,\n    var(--transition-time) text-decoration-color,\n    var(--transition-time) box-shadow, var(--transition-time) transform;\n\n  --button-color: white;\n  --button-background: var(--background);\n  --button-border: 1px solid white;\n  --button-hover-background: var(--color-primored);\n  --button-padding: 8px 20px;\n  --button-border-radius: 5px;\n\n  --padding: 2rem;\n\n  color: var(--body-color);\n  background: var(--background);\n  font-family: \"Inter\", system-ui, sans-serif;\n  transition: var(--transition);\n}\n\n#page[lang=\"ar\"] {\n    direction: rtl;\n  }\n\n#page{\n  font-weight: 300;\n  font-size: 1.125rem;\n  line-height: 1.2;\n}\n\n.section-container {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding-left: var(--padding);\n  padding-right: var(--padding);\n  padding-top: 5rem;\n  padding-bottom: 5rem;\n}\n\n.button {\n  display: flex;\n  align-items: center;\n  justify-content: center;\n  gap: 0.25rem;\n  color: var(--button-color);\n  border: var(--button-border);\n  border-radius: 6px;\n  padding: var(--button-padding);\n  transition: var(--transition);\n  transform: translateY(0);\n  font-weight: 400;\n}\n\n.button.secondary {\n    border: 0;\n    color: var(--color-white);\n    background: var(--color-gray);\n  }\n\n.button.is-primary {\n    border: 1.5px solid var(--color-accent);\n  }\n\n.button.small {\n    color: var(--color);\n    padding: 0.25rem 0.75rem 0.25rem 0.25rem;\n    font-size: 0.75rem;\n    background: transparent;\n    border: 1.5px solid var(--border-color);\n    display: flex;\n    margin-bottom: 1rem;\n  }\n\n.button.small svg {\n      width: 1rem;\n      height: 1rem;\n    }\n\n.button:hover {\n    border-color: transparent;\n    background: var(--color-background);\n    color: white;\n    box-shadow: 0 0 0 2px var(--color-accent);\n  }\n\n.button.disabled {\n    cursor: disabled;\n    opacity: 0.5;\n    pointer-events: none;\n  }\n\n.heading {\n  font-family: \"Archivo\", system-ui, sans-serif;\n  font-size: var(--heading-font-size, 49px);\n  line-height: var(--heading-line-height, 1.15);\n  font-weight: var(--heading-font-weight, 500);\n  color: var(--heading-color, #252428);\n  text-align: center;\n}\n\nh2.heading {\n  line-height: 1.15;\n  font-size: 2.5rem;\n}\n\n.subheading {\n  text-align: center;\n  font-size: 1.125rem;\n}\n\n.link {\n  transition: border-color 0.1s;\n}\n\n.link:hover {\n    border-color: transparent;\n  }\n\n.link.underlined {\n    border-bottom: 2px solid var(--color-accent, #154bf4);\n  }\n\n.link.underlined:hover {\n      border-color: transparent;\n    }\n\n.link.arrow {\n    display: inline-flex;\n    align-items: center;\n    color: var(--color-accent);\n    font-weight: 500;\n  }\n\n.link.arrow svg {\n      transition: 0.1s transform;\n      transform: translateX(0);\n      position: relative;\n      top: 2px;\n    }\n\n.link.arrow span {\n      margin-right: 0.5rem;\n    }\n\n.link.arrow:hover svg {\n      transform: translateX(4px);\n    }\n\n.content blockquote {\n    padding: 2rem;\n    border-left: 5px solid var(--border-color);\n    margin: 2rem 0;\n    font-size: 1.5rem;\n  }\n\n.content h1 {\n    font-family: \"Archivo\", system-ui, sans-serif;\n    color: var(--color);\n    font-size: 2.5rem;\n    font-weight: 600;\n    margin-bottom: 1rem;\n    font-weight: 700;\n    letter-spacing: -0.01em;\n  }\n\n.content h2 {\n    font-family: \"Archivo\", system-ui, sans-serif;\n    color: var(--color);\n    font-size: 2.25rem;\n    font-weight: 600;\n    line-height: 1.3;\n    margin-top: 3rem;\n    margin-bottom: 1rem;\n  }\n\n.content h2 + h3 {\n    margin-top: 0;\n  }\n\n.content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    padding-bottom: .5rem;\n    margin-top: 2rem;\n  }\n\n.content h4 {\n    font-size: 1.25rem;\n    font-weight: 600;\n    line-height: 1;\n    margin-bottom: .5rem;\n  }\n\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n  }\n\n.content p {\n    line-height: 1.4;\n    font-size: 1.125rem;\n    font-weight: 300;\n  }\n\n.content p:not(:last-child) {\n      margin-bottom: 1rem;\n    }\n\n.content ol {\n    list-style: decimal;\n    padding-left: 1.25rem;\n  }\n\n.content ul {\n    list-style: disc;\n    padding-left: 1.25rem;\n    margin-bottom: 1rem;\n  }\n\n.content ul li {\n      padding: 0.25rem 0;\n    }\n\n.content strong {\n    font-weight: 500;\n    color: #35\n  }\n\n.content hr {\n    border-color: var(--border-color); \n    margin-block: 5rem; \n  }\n\n.content a {\n    border-bottom: 2px solid var(--color-accent);\n\n  }\n\nform {\n  display: grid;\n  gap: 1rem;\n}\n\nform label {\n    display: grid;\n    gap: 0.25rem;\n  }\n\nform label span {\n      font-size: 0.75rem;\n      font-weight: 500;\n    }\n\nform label input,\n    form label textarea {\n      padding: 0.5rem;\n      outline-color: transparent;\n      color: #222;\n      transition: var(--transition, 0.1s outline-color);\n      border: 1.5px solid var(--border-color, #eee);\n      border-radius: var(--border-radius);\n    }\n\nform label input:focus, form label textarea:focus {\n        outline-color: var(--color-accent, rebeccapurple);\n      }\n\nform label input::-moz-placeholder, form label textarea::-moz-placeholder {\n        font-weight: 300;\n      }\n\nform label input:-ms-input-placeholder, form label textarea:-ms-input-placeholder {\n        font-weight: 300;\n      }\n\nform label input::placeholder, form label textarea::placeholder {\n        font-weight: 300;\n      }\n\nform .button {\n    margin-top: 0.5rem;\n    display: flex;\n    justify-content: center; \n    font-weight: 400;\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1l7xqc8', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link = claim_element(head_nodes, "LINK", { rel: true, type: true, href: true });
			meta2 = claim_element(head_nodes, "META", { name: true, content: true });
			script = claim_element(head_nodes, "SCRIPT", { "data-domain": true, src: true });
			var script_nodes = children(script);
			script_nodes.forEach(detach);
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/tailwindcss@2.2.15/dist/base.css\");\n@import url(https://fonts.bunny.net/css?family=archivo:200,300,300i,400,400i,500,500i,600,600i,700,700i);\n\n#page {\n  --color-primored: #35d994;\n  --color-gray: #262626;\n  --color-black: #121212;\n  --color-white: #ffff;\n  --color-accent: var(--color-primored);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.1);\n\n  --padding-left: 2rem;\n  --padding-right: 2rem;\n\n  --color: #F3F3F3;\n  --background: var(--color-black);\n  --max-width: 1000px;\n  --border-color: var(--color-gray);\n  --border: 2px solid var(--border-color);\n  --border-radius: 5px;\n\n  --heading-font-size: clamp(1rem, 10vw, 2.25rem);\n  --heading-color: #FDFDFD;\n  --heading-font-weight: 600;\n  --heading-line-height: 1.3;\n  --subheading-color: #DADADA;\n  --body-color: #CECECE;\n  --heading-line-height: 1.3;\n\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color, var(--transition-time) background,\n    var(--transition-time) border-color,\n    var(--transition-time) text-decoration-color,\n    var(--transition-time) box-shadow, var(--transition-time) transform;\n\n  --button-color: white;\n  --button-background: var(--background);\n  --button-border: 1px solid white;\n  --button-hover-background: var(--color-primored);\n  --button-padding: 8px 20px;\n  --button-border-radius: 5px;\n\n  --padding: 2rem;\n\n  color: var(--body-color);\n  background: var(--background);\n  font-family: \"Inter\", system-ui, sans-serif;\n  transition: var(--transition);\n}\n\n#page[lang=\"ar\"] {\n    direction: rtl;\n  }\n\n#page{\n  font-weight: 300;\n  font-size: 1.125rem;\n  line-height: 1.2;\n}\n\n.section-container {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding-left: var(--padding);\n  padding-right: var(--padding);\n  padding-top: 5rem;\n  padding-bottom: 5rem;\n}\n\n.button {\n  display: flex;\n  align-items: center;\n  justify-content: center;\n  gap: 0.25rem;\n  color: var(--button-color);\n  border: var(--button-border);\n  border-radius: 6px;\n  padding: var(--button-padding);\n  transition: var(--transition);\n  transform: translateY(0);\n  font-weight: 400;\n}\n\n.button.secondary {\n    border: 0;\n    color: var(--color-white);\n    background: var(--color-gray);\n  }\n\n.button.is-primary {\n    border: 1.5px solid var(--color-accent);\n  }\n\n.button.small {\n    color: var(--color);\n    padding: 0.25rem 0.75rem 0.25rem 0.25rem;\n    font-size: 0.75rem;\n    background: transparent;\n    border: 1.5px solid var(--border-color);\n    display: flex;\n    margin-bottom: 1rem;\n  }\n\n.button.small svg {\n      width: 1rem;\n      height: 1rem;\n    }\n\n.button:hover {\n    border-color: transparent;\n    background: var(--color-background);\n    color: white;\n    box-shadow: 0 0 0 2px var(--color-accent);\n  }\n\n.button.disabled {\n    cursor: disabled;\n    opacity: 0.5;\n    pointer-events: none;\n  }\n\n.heading {\n  font-family: \"Archivo\", system-ui, sans-serif;\n  font-size: var(--heading-font-size, 49px);\n  line-height: var(--heading-line-height, 1.15);\n  font-weight: var(--heading-font-weight, 500);\n  color: var(--heading-color, #252428);\n  text-align: center;\n}\n\nh2.heading {\n  line-height: 1.15;\n  font-size: 2.5rem;\n}\n\n.subheading {\n  text-align: center;\n  font-size: 1.125rem;\n}\n\n.link {\n  transition: border-color 0.1s;\n}\n\n.link:hover {\n    border-color: transparent;\n  }\n\n.link.underlined {\n    border-bottom: 2px solid var(--color-accent, #154bf4);\n  }\n\n.link.underlined:hover {\n      border-color: transparent;\n    }\n\n.link.arrow {\n    display: inline-flex;\n    align-items: center;\n    color: var(--color-accent);\n    font-weight: 500;\n  }\n\n.link.arrow svg {\n      transition: 0.1s transform;\n      transform: translateX(0);\n      position: relative;\n      top: 2px;\n    }\n\n.link.arrow span {\n      margin-right: 0.5rem;\n    }\n\n.link.arrow:hover svg {\n      transform: translateX(4px);\n    }\n\n.content blockquote {\n    padding: 2rem;\n    border-left: 5px solid var(--border-color);\n    margin: 2rem 0;\n    font-size: 1.5rem;\n  }\n\n.content h1 {\n    font-family: \"Archivo\", system-ui, sans-serif;\n    color: var(--color);\n    font-size: 2.5rem;\n    font-weight: 600;\n    margin-bottom: 1rem;\n    font-weight: 700;\n    letter-spacing: -0.01em;\n  }\n\n.content h2 {\n    font-family: \"Archivo\", system-ui, sans-serif;\n    color: var(--color);\n    font-size: 2.25rem;\n    font-weight: 600;\n    line-height: 1.3;\n    margin-top: 3rem;\n    margin-bottom: 1rem;\n  }\n\n.content h2 + h3 {\n    margin-top: 0;\n  }\n\n.content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    padding-bottom: .5rem;\n    margin-top: 2rem;\n  }\n\n.content h4 {\n    font-size: 1.25rem;\n    font-weight: 600;\n    line-height: 1;\n    margin-bottom: .5rem;\n  }\n\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n  }\n\n.content p {\n    line-height: 1.4;\n    font-size: 1.125rem;\n    font-weight: 300;\n  }\n\n.content p:not(:last-child) {\n      margin-bottom: 1rem;\n    }\n\n.content ol {\n    list-style: decimal;\n    padding-left: 1.25rem;\n  }\n\n.content ul {\n    list-style: disc;\n    padding-left: 1.25rem;\n    margin-bottom: 1rem;\n  }\n\n.content ul li {\n      padding: 0.25rem 0;\n    }\n\n.content strong {\n    font-weight: 500;\n    color: #35\n  }\n\n.content hr {\n    border-color: var(--border-color); \n    margin-block: 5rem; \n  }\n\n.content a {\n    border-bottom: 2px solid var(--color-accent);\n\n  }\n\nform {\n  display: grid;\n  gap: 1rem;\n}\n\nform label {\n    display: grid;\n    gap: 0.25rem;\n  }\n\nform label span {\n      font-size: 0.75rem;\n      font-weight: 500;\n    }\n\nform label input,\n    form label textarea {\n      padding: 0.5rem;\n      outline-color: transparent;\n      color: #222;\n      transition: var(--transition, 0.1s outline-color);\n      border: 1.5px solid var(--border-color, #eee);\n      border-radius: var(--border-radius);\n    }\n\nform label input:focus, form label textarea:focus {\n        outline-color: var(--color-accent, rebeccapurple);\n      }\n\nform label input::-moz-placeholder, form label textarea::-moz-placeholder {\n        font-weight: 300;\n      }\n\nform label input:-ms-input-placeholder, form label textarea:-ms-input-placeholder {\n        font-weight: 300;\n      }\n\nform label input::placeholder, form label textarea::placeholder {\n        font-weight: 300;\n      }\n\nform .button {\n    margin-top: 0.5rem;\n    display: flex;\n    justify-content: center; \n    font-weight: 400;\n  }");
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
	let { test } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(1, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('test' in $$props) $$invalidate(3, test = $$props.test);
	};

	return [title, favicon, description, test];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			title: 0,
			favicon: 1,
			description: 2,
			test: 3
		});
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

/* generated by Svelte v3.59.1 */

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

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	child_ctx[10] = list[i].links;
	const constants_0 = /*links*/ child_ctx[10].length > 0;
	child_ctx[11] = constants_0;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	child_ctx[10] = list[i].links;
	child_ctx[16] = list[i].featured;
	const constants_0 = /*links*/ child_ctx[10].length > 0;
	child_ctx[11] = constants_0;
	return child_ctx;
}

function get_each_context_3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (249:12) {#if banner.label}
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
			attr(div0, "class", "memo-content svelte-17esy5a");
			attr(div1, "class", "banner svelte-17esy5a");
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

// (253:6) {#if banner.cta.label}
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
			attr(a, "class", "svelte-17esy5a");
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

// (276:10) {#if featured}
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
			attr(span, "class", "featured-pill svelte-17esy5a");
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

// (282:10) {:else}
function create_else_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
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
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
			attr(a, "class", "link svelte-17esy5a");
			toggle_class(a, "active", /*link*/ ctx[9].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*nav, window*/ 4) {
				toggle_class(a, "active", /*link*/ ctx[9].url === window.location.pathname);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (279:10) {#if hasDropdown}
function create_if_block_3(ctx) {
	let span0;
	let t0_value = /*link*/ ctx[9].label + "";
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
			attr(span0, "class", "svelte-17esy5a");
			attr(span1, "class", "icon svelte-17esy5a");
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
			if ((!current || dirty & /*nav*/ 4) && t0_value !== (t0_value = /*link*/ ctx[9].label + "")) set_data(t0, t0_value);
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

// (289:8) {#if hasDropdown}
function create_if_block_2(ctx) {
	let div;
	let each_value_3 = /*links*/ ctx[10];
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
			attr(div, "class", "dropdown svelte-17esy5a");
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
				each_value_3 = /*links*/ ctx[10];
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

// (291:12) {#each links as { link }}
function create_each_block_3(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
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
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
			attr(a, "class", "link svelte-17esy5a");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (272:4) {#each nav as { link, links, featured }}
function create_each_block_2(ctx) {
	let div1;
	let div0;
	let t0;
	let current_block_type_index;
	let if_block1;
	let t1;
	let current;
	let if_block0 = /*featured*/ ctx[16] && create_if_block_4();
	const if_block_creators = [create_if_block_3, create_else_block_1];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*hasDropdown*/ ctx[11]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type(ctx);
	if_block1 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	let if_block2 = /*hasDropdown*/ ctx[11] && create_if_block_2(ctx);

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
			attr(div0, "class", "top-link svelte-17esy5a");
			attr(div1, "class", "nav-item svelte-17esy5a");
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
			if (/*featured*/ ctx[16]) {
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

			if (/*hasDropdown*/ ctx[11]) {
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

// (302:2) {#if mobileNavOpen}
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
			attr(button, "class", "svelte-17esy5a");
			attr(nav_1, "id", "mobile-nav");
			attr(nav_1, "class", "svelte-17esy5a");
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

// (310:8) {:else}
function create_else_block$1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
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
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
			attr(a, "class", "link svelte-17esy5a");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (306:8) {#if hasDropdown}
function create_if_block_1$1(ctx) {
	let each_1_anchor;
	let each_value_1 = /*links*/ ctx[10];
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
				each_value_1 = /*links*/ ctx[10];
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

// (307:10) {#each links as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
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
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
			attr(a, "class", "link svelte-17esy5a");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 4 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (304:6) {#each nav as { link, links }}
function create_each_block(ctx) {
	let if_block_anchor;

	function select_block_type_1(ctx, dirty) {
		if (/*hasDropdown*/ ctx[11]) return create_if_block_1$1;
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
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
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
			this.h();
		},
		h() {
			attr(span0, "class", "svelte-17esy5a");
			html_tag.a = null;
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-17esy5a");
			attr(span1, "class", "svelte-17esy5a");
			attr(a1, "class", "link pill svelte-17esy5a");
			attr(a1, "href", "https://github.com/primocms/primo");
			attr(a1, "aria-label", "Github repo");
			attr(div0, "class", "menu-icon svelte-17esy5a");
			attr(button, "id", "open");
			attr(button, "class", "svelte-17esy5a");
			attr(nav_1, "class", "svelte-17esy5a");
			attr(header, "class", "section-container svelte-17esy5a");
			attr(div1, "class", "section");
			attr(div1, "id", "section-84b75474");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
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
			if (detaching) detach(div1);
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
	let { test } = $$props;
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
		if ('test' in $$props) $$invalidate(8, test = $$props.test);
		if ('banner' in $$props) $$invalidate(0, banner = $$props.banner);
		if ('logo' in $$props) $$invalidate(1, logo = $$props.logo);
		if ('nav' in $$props) $$invalidate(2, nav = $$props.nav);
	};

	return [
		banner,
		logo,
		nav,
		mobileNavOpen,
		toggleMobileNav,
		title,
		favicon,
		description,
		test
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			title: 5,
			favicon: 6,
			description: 7,
			test: 8,
			banner: 0,
			logo: 1,
			nav: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$3(ctx) {
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";
	let div0_style_value;
	let t;
	let link;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			t = space();
			link = element("link");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);

			div0 = claim_element(div1_nodes, "DIV", {
				class: true,
				"data-key": true,
				style: true
			});

			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t = claim_space(div1_nodes);
			link = claim_element(div1_nodes, "LINK", { type: true, href: true });
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-gbuzio");
			attr(div0, "data-key", "content");

			attr(div0, "style", div0_style_value = `
--heading-align: ${/*style*/ ctx[1].center_heading ? 'center' : 'left'}`);

			attr(link, "type", "text/css");
			attr(link, "href", "https://unpkg.com/highlightjs@9.16.2/styles/foundation.css");
			attr(div1, "class", "section");
			attr(div1, "id", "section-9980257d");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div1, t);
			append_hydration(div1, link);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*style*/ 2 && div0_style_value !== (div0_style_value = `
--heading-align: ${/*style*/ ctx[1].center_heading ? 'center' : 'left'}`)) {
				attr(div0, "style", div0_style_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { test } = $$props;
	let { content } = $$props;
	let { style } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('test' in $$props) $$invalidate(5, test = $$props.test);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
		if ('style' in $$props) $$invalidate(1, style = $$props.style);
	};

	return [content, style, title, favicon, description, test];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			title: 2,
			favicon: 3,
			description: 4,
			test: 5,
			content: 0,
			style: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$4(ctx) {
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
			div14 = claim_element(nodes, "DIV", { class: true, id: true });
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
			attr(div14, "class", "section");
			attr(div14, "id", "section-153455ec");
		},
		m(target, anchor) {
			insert_hydration(target, div14, anchor);
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
			if (detaching) detach(div14);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { test } = $$props;
	let { signup_form } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(3, description = $$props.description);
		if ('test' in $$props) $$invalidate(4, test = $$props.test);
		if ('signup_form' in $$props) $$invalidate(0, signup_form = $$props.signup_form);
	};

	return [signup_form, title, favicon, description, test];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			title: 1,
			favicon: 2,
			description: 3,
			test: 4,
			signup_form: 0
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	child_ctx[10] = list[i].icon;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (109:8) {#each footer_nav as { link }}
function create_each_block_1$1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
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
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
			attr(a, "class", "svelte-13um1f6");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_nav*/ 1 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*footer_nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (120:6) {#each social as { link, icon }}
function create_each_block$1(ctx) {
	let li;
	let a;
	let icon;
	let a_href_value;
	let a_aria_label_value;
	let t;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[10] } });

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
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
			attr(a, "aria-label", a_aria_label_value = /*link*/ ctx[9].label);
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
			if (dirty & /*social*/ 2) icon_changes.icon = /*icon*/ ctx[10];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social*/ 2 && a_aria_label_value !== (a_aria_label_value = /*link*/ ctx[9].label)) {
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

function create_fragment$5(ctx) {
	let div2;
	let footer;
	let div1;
	let div0;
	let nav;
	let t;
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
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div2 = element("div");
			footer = element("footer");
			div1 = element("div");
			div0 = element("div");
			nav = element("nav");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			footer = claim_element(div2_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div1 = claim_element(footer_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav, "class", "svelte-13um1f6");
			attr(div0, "class", "container svelte-13um1f6");
			attr(ul, "class", "svelte-13um1f6");
			attr(div1, "class", "section-container svelte-13um1f6");
			attr(footer, "class", "svelte-13um1f6");
			attr(div2, "class", "section");
			attr(div2, "id", "section-225b32e4");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, footer);
			append_hydration(footer, div1);
			append_hydration(div1, div0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav, null);
				}
			}

			append_hydration(div1, t);
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
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
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
			if (detaching) detach(div2);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { test } = $$props;
	let { footer_nav } = $$props;
	let { social } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('test' in $$props) $$invalidate(5, test = $$props.test);
		if ('footer_nav' in $$props) $$invalidate(0, footer_nav = $$props.footer_nav);
		if ('social' in $$props) $$invalidate(1, social = $$props.social);
	};

	return [footer_nav, social, title, favicon, description, test];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			title: 2,
			favicon: 3,
			description: 4,
			test: 5,
			footer_nav: 0,
			social: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function instance$6($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { favicon } = $$props;
	let { description } = $$props;
	let { test } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('favicon' in $$props) $$invalidate(1, favicon = $$props.favicon);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('test' in $$props) $$invalidate(3, test = $$props.test);
	};

	return [title, favicon, description, test];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, null, safe_not_equal, {
			title: 0,
			favicon: 1,
			description: 2,
			test: 3
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$6(ctx) {
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
				description: "Primo is a visual CMS that makes it a blast to build pages, manage content, and edit code - one block at a time.",
				test: "THE TEST VALUE"
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
				test: "THE TEST VALUE",
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
						"link": { "url": "/about", "label": "About" },
						"links": [
							{
								"link": {
									"url": "/about/why",
									"label": "Why Primo"
								}
							},
							{
								"link": {
									"url": "/about/mission",
									"label": "Mission"
								}
							},
							{
								"link": {
									"url": "/about/how-it-works",
									"label": "How it Works"
								}
							}
						],
						"featured": ""
					},
					{
						"link": {
							"url": "https://docs.primocms.org",
							"label": "Docs"
						},
						"links": [],
						"featured": false
					},
					{
						"link": {
							"url": "/themes",
							"label": "Themes",
							"active": false
						},
						"links": [],
						"featured": false
					},
					{
						"link": {
							"url": "/white-glove",
							"label": "White Glove"
						},
						"links": [],
						"featured": false
					},
					{
						"link": { "url": "/cloud", "label": "Cloud" },
						"links": [],
						"featured": true
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
				test: "THE TEST VALUE",
				content: {
					"html": "<h1>How it works</h1><p>Primo is a <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link\" href=\"https://kit.svelte.dev/\">SvelteKit</a> application which uses <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link\" href=\"https://supabase.com/\">Supabase</a> as a backend for authentication, a database, and file storage. Sites, pages, blocks, and block instances (i.e. pages sections) are all stored in a <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link\" href=\"https://www.postgresql.org/\">Postgres</a> database as individual rows containing code, fields, and content.</p><p>On-page editing works by matching a block's field values to text, link, and image values or explicitly set <code>data-key</code> attributes within the block's rendered HTML. Editable text is powered by <code>contentEditable = true</code> and a <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link\" href=\"https://tiptap.dev/\">TipTap</a>/<a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link\" href=\"https://prosemirror.net/\">ProseMirror</a> editor for <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link\" href=\"https://www.markdownguide.org/\">Markdown</a> fields. The dev environment is powered by <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link\" href=\"https://codemirror.net/\">CodeMirror</a>.</p><p>Rollup and the <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link\" href=\"https://svelte.dev\">Svelte</a> compiler are used to compile page blocks into Svelte components (alongside PostCSS for nesting) and to build the static files for the deployed website, which Primo then uploads to Github via its REST API.</p>",
					"markdown": "# How it works\n\nPrimo is a [SvelteKit](<https://kit.svelte.dev/>) application which uses [Supabase](<https://supabase.com/>) as a backend for authentication, a database, and file storage. Sites, pages, blocks, and block instances (i.e. pages sections) are all stored in a [Postgres](<https://www.postgresql.org/>) database as individual rows containing code, fields, and content.\n\nOn-page editing works by matching a block's field values to text, link, and image values or explicitly set `data-key` attributes within the block's rendered HTML. Editable text is powered by `contentEditable = true` and a [TipTap](<https://tiptap.dev/>)/[ProseMirror](<https://prosemirror.net/>) editor for [Markdown](<https://www.markdownguide.org/>) fields. The dev environment is powered by [CodeMirror](<https://codemirror.net/>).\n\nRollup and the [Svelte](<https://svelte.dev>) compiler are used to compile page blocks into Svelte components (alongside PostCSS for nesting) and to build the static files for the deployed website, which Primo then uploads to Github via its REST API.\n\n"
				},
				style: { "center_heading": "" }
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
				test: "THE TEST VALUE",
				signup_form: {
					"heading": "Hear about future updates, including:",
					"subheading": {
						"html": "<ul><li><p><strong>Using it headless</strong> alongside SvelteKit, NextJS, etc.</p></li><li><p><strong>Design fields</strong> to give content editors predefined style options.</p></li><li><p><strong>Cloud functions</strong> for writing backend code from Primo.</p></li></ul>",
						"markdown": "- **Using it headless** alongside SvelteKit, NextJS, etc.\n\n- **Design fields** to give content editors predefined style options.\n\n- **Cloud functions** for writing backend code from Primo.\n\n\n<!-- -->\n\n"
					}
				}
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
				test: "THE TEST VALUE",
				footer_nav: [
					{
						"link": { "url": "/", "label": "Changelog" }
					}
				],
				social: [
					{
						"icon": "fa6-brands:discourse",
						"link": {
							"url": "https://forum.primo.so ",
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
							"url": "https://www.youtube.com/@primocms ",
							"label": "Youtube"
						}
					},
					{
						"icon": "fa6-brands:github",
						"link": {
							"url": "https://github.com/primocms/primo ",
							"label": "Github"
						}
					}
				]
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
				test: "THE TEST VALUE"
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
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
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
		}
	};
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$6, safe_not_equal, {});
	}
}

export default Component$7;
