// Page List - Updated May 19, 2024
function noop() { }
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
// Adapted from https://github.com/then/is-promise/blob/master/index.js
// Distributed under MIT License https://github.com/then/is-promise/blob/master/LICENSE
function is_promise(value) {
    return !!value && (typeof value === 'object' || typeof value === 'function') && typeof value.then === 'function';
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
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
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

function handle_promise(promise, info) {
    const token = info.token = {};
    function update(type, index, key, value) {
        if (info.token !== token)
            return;
        info.resolved = value;
        let child_ctx = info.ctx;
        if (key !== undefined) {
            child_ctx = child_ctx.slice();
            child_ctx[key] = value;
        }
        const block = type && (info.current = type)(child_ctx);
        let needs_flush = false;
        if (info.block) {
            if (info.blocks) {
                info.blocks.forEach((block, i) => {
                    if (i !== index && block) {
                        group_outros();
                        transition_out(block, 1, 1, () => {
                            if (info.blocks[i] === block) {
                                info.blocks[i] = null;
                            }
                        });
                        check_outros();
                    }
                });
            }
            else {
                info.block.d(1);
            }
            block.c();
            transition_in(block, 1);
            block.m(info.mount(), info.anchor);
            needs_flush = true;
        }
        info.block = block;
        if (info.blocks)
            info.blocks[index] = block;
        if (needs_flush) {
            flush();
        }
    }
    if (is_promise(promise)) {
        const current_component = get_current_component();
        promise.then(value => {
            set_current_component(current_component);
            update(info.then, 1, info.value, value);
            set_current_component(null);
        }, error => {
            set_current_component(current_component);
            update(info.catch, 2, info.error, error);
            set_current_component(null);
            if (!info.hasCatch) {
                throw error;
            }
        });
        // if we previously had a then/catch block, destroy it
        if (info.current !== info.pending) {
            update(info.pending, 0);
            return true;
        }
    }
    else {
        if (info.current !== info.then) {
            update(info.then, 1, info.value, promise);
            return true;
        }
        info.resolved = promise;
    }
}
function update_await_block_branch(info, ctx, dirty) {
    const child_ctx = ctx.slice();
    const { resolved } = info;
    if (info.current === info.then) {
        child_ctx[info.value] = resolved;
    }
    if (info.current === info.catch) {
        child_ctx[info.error] = resolved;
    }
    info.block.p(child_ctx, dirty);
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

const exports = {}; const module = { exports };

!function(e,t){"object"==typeof exports&&"undefined"!=typeof module?module.exports=t():"function"==typeof define&&define.amd?define(t):(e="undefined"!=typeof globalThis?globalThis:e||self).axios=t();}(undefined,(function(){function e(e,t){var r=Object.keys(e);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(e);t&&(n=n.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),r.push.apply(r,n);}return r}function t(t){for(var r=1;r<arguments.length;r++){var n=null!=arguments[r]?arguments[r]:{};r%2?e(Object(n),!0).forEach((function(e){c(t,e,n[e]);})):Object.getOwnPropertyDescriptors?Object.defineProperties(t,Object.getOwnPropertyDescriptors(n)):e(Object(n)).forEach((function(e){Object.defineProperty(t,e,Object.getOwnPropertyDescriptor(n,e));}));}return t}function r(){r=function(){return t};var e,t={},n=Object.prototype,o=n.hasOwnProperty,i=Object.defineProperty||function(e,t,r){e[t]=r.value;},a="function"==typeof Symbol?Symbol:{},s=a.iterator||"@@iterator",u=a.asyncIterator||"@@asyncIterator",c=a.toStringTag||"@@toStringTag";function f(e,t,r){return Object.defineProperty(e,t,{value:r,enumerable:!0,configurable:!0,writable:!0}),e[t]}try{f({},"");}catch(e){f=function(e,t,r){return e[t]=r};}function l(e,t,r,n){var o=t&&t.prototype instanceof m?t:m,a=Object.create(o.prototype),s=new N(n||[]);return i(a,"_invoke",{value:A(e,r,s)}),a}function h(e,t,r){try{return {type:"normal",arg:e.call(t,r)}}catch(e){return {type:"throw",arg:e}}}t.wrap=l;var p="suspendedStart",d="executing",y="completed",v={};function m(){}function g(){}function b(){}var w={};f(w,s,(function(){return this}));var E=Object.getPrototypeOf,O=E&&E(E(k([])));O&&O!==n&&o.call(O,s)&&(w=O);var S=b.prototype=m.prototype=Object.create(w);function j(e){["next","throw","return"].forEach((function(t){f(e,t,(function(e){return this._invoke(t,e)}));}));}function R(e,t){function r(n,i,a,s){var u=h(e[n],e,i);if("throw"!==u.type){var c=u.arg,f=c.value;return f&&"object"==typeof f&&o.call(f,"__await")?t.resolve(f.__await).then((function(e){r("next",e,a,s);}),(function(e){r("throw",e,a,s);})):t.resolve(f).then((function(e){c.value=e,a(c);}),(function(e){return r("throw",e,a,s)}))}s(u.arg);}var n;i(this,"_invoke",{value:function(e,o){function i(){return new t((function(t,n){r(e,o,t,n);}))}return n=n?n.then(i,i):i()}});}function A(t,r,n){var o=p;return function(i,a){if(o===d)throw new Error("Generator is already running");if(o===y){if("throw"===i)throw a;return {value:e,done:!0}}for(n.method=i,n.arg=a;;){var s=n.delegate;if(s){var u=T(s,n);if(u){if(u===v)continue;return u}}if("next"===n.method)n.sent=n._sent=n.arg;else if("throw"===n.method){if(o===p)throw o=y,n.arg;n.dispatchException(n.arg);}else "return"===n.method&&n.abrupt("return",n.arg);o=d;var c=h(t,r,n);if("normal"===c.type){if(o=n.done?y:"suspendedYield",c.arg===v)continue;return {value:c.arg,done:n.done}}"throw"===c.type&&(o=y,n.method="throw",n.arg=c.arg);}}}function T(t,r){var n=r.method,o=t.iterator[n];if(o===e)return r.delegate=null,"throw"===n&&t.iterator.return&&(r.method="return",r.arg=e,T(t,r),"throw"===r.method)||"return"!==n&&(r.method="throw",r.arg=new TypeError("The iterator does not provide a '"+n+"' method")),v;var i=h(o,t.iterator,r.arg);if("throw"===i.type)return r.method="throw",r.arg=i.arg,r.delegate=null,v;var a=i.arg;return a?a.done?(r[t.resultName]=a.value,r.next=t.nextLoc,"return"!==r.method&&(r.method="next",r.arg=e),r.delegate=null,v):a:(r.method="throw",r.arg=new TypeError("iterator result is not an object"),r.delegate=null,v)}function x(e){var t={tryLoc:e[0]};1 in e&&(t.catchLoc=e[1]),2 in e&&(t.finallyLoc=e[2],t.afterLoc=e[3]),this.tryEntries.push(t);}function P(e){var t=e.completion||{};t.type="normal",delete t.arg,e.completion=t;}function N(e){this.tryEntries=[{tryLoc:"root"}],e.forEach(x,this),this.reset(!0);}function k(t){if(t||""===t){var r=t[s];if(r)return r.call(t);if("function"==typeof t.next)return t;if(!isNaN(t.length)){var n=-1,i=function r(){for(;++n<t.length;)if(o.call(t,n))return r.value=t[n],r.done=!1,r;return r.value=e,r.done=!0,r};return i.next=i}}throw new TypeError(typeof t+" is not iterable")}return g.prototype=b,i(S,"constructor",{value:b,configurable:!0}),i(b,"constructor",{value:g,configurable:!0}),g.displayName=f(b,c,"GeneratorFunction"),t.isGeneratorFunction=function(e){var t="function"==typeof e&&e.constructor;return !!t&&(t===g||"GeneratorFunction"===(t.displayName||t.name))},t.mark=function(e){return Object.setPrototypeOf?Object.setPrototypeOf(e,b):(e.__proto__=b,f(e,c,"GeneratorFunction")),e.prototype=Object.create(S),e},t.awrap=function(e){return {__await:e}},j(R.prototype),f(R.prototype,u,(function(){return this})),t.AsyncIterator=R,t.async=function(e,r,n,o,i){void 0===i&&(i=Promise);var a=new R(l(e,r,n,o),i);return t.isGeneratorFunction(r)?a:a.next().then((function(e){return e.done?e.value:a.next()}))},j(S),f(S,c,"Generator"),f(S,s,(function(){return this})),f(S,"toString",(function(){return "[object Generator]"})),t.keys=function(e){var t=Object(e),r=[];for(var n in t)r.push(n);return r.reverse(),function e(){for(;r.length;){var n=r.pop();if(n in t)return e.value=n,e.done=!1,e}return e.done=!0,e}},t.values=k,N.prototype={constructor:N,reset:function(t){if(this.prev=0,this.next=0,this.sent=this._sent=e,this.done=!1,this.delegate=null,this.method="next",this.arg=e,this.tryEntries.forEach(P),!t)for(var r in this)"t"===r.charAt(0)&&o.call(this,r)&&!isNaN(+r.slice(1))&&(this[r]=e);},stop:function(){this.done=!0;var e=this.tryEntries[0].completion;if("throw"===e.type)throw e.arg;return this.rval},dispatchException:function(t){if(this.done)throw t;var r=this;function n(n,o){return s.type="throw",s.arg=t,r.next=n,o&&(r.method="next",r.arg=e),!!o}for(var i=this.tryEntries.length-1;i>=0;--i){var a=this.tryEntries[i],s=a.completion;if("root"===a.tryLoc)return n("end");if(a.tryLoc<=this.prev){var u=o.call(a,"catchLoc"),c=o.call(a,"finallyLoc");if(u&&c){if(this.prev<a.catchLoc)return n(a.catchLoc,!0);if(this.prev<a.finallyLoc)return n(a.finallyLoc)}else if(u){if(this.prev<a.catchLoc)return n(a.catchLoc,!0)}else {if(!c)throw new Error("try statement without catch or finally");if(this.prev<a.finallyLoc)return n(a.finallyLoc)}}}},abrupt:function(e,t){for(var r=this.tryEntries.length-1;r>=0;--r){var n=this.tryEntries[r];if(n.tryLoc<=this.prev&&o.call(n,"finallyLoc")&&this.prev<n.finallyLoc){var i=n;break}}i&&("break"===e||"continue"===e)&&i.tryLoc<=t&&t<=i.finallyLoc&&(i=null);var a=i?i.completion:{};return a.type=e,a.arg=t,i?(this.method="next",this.next=i.finallyLoc,v):this.complete(a)},complete:function(e,t){if("throw"===e.type)throw e.arg;return "break"===e.type||"continue"===e.type?this.next=e.arg:"return"===e.type?(this.rval=this.arg=e.arg,this.method="return",this.next="end"):"normal"===e.type&&t&&(this.next=t),v},finish:function(e){for(var t=this.tryEntries.length-1;t>=0;--t){var r=this.tryEntries[t];if(r.finallyLoc===e)return this.complete(r.completion,r.afterLoc),P(r),v}},catch:function(e){for(var t=this.tryEntries.length-1;t>=0;--t){var r=this.tryEntries[t];if(r.tryLoc===e){var n=r.completion;if("throw"===n.type){var o=n.arg;P(r);}return o}}throw new Error("illegal catch attempt")},delegateYield:function(t,r,n){return this.delegate={iterator:k(t),resultName:r,nextLoc:n},"next"===this.method&&(this.arg=e),v}},t}function n(e){var t=function(e,t){if("object"!=typeof e||!e)return e;var r=e[Symbol.toPrimitive];if(void 0!==r){var n=r.call(e,t||"default");if("object"!=typeof n)return n;throw new TypeError("@@toPrimitive must return a primitive value.")}return ("string"===t?String:Number)(e)}(e,"string");return "symbol"==typeof t?t:String(t)}function o(e){return o="function"==typeof Symbol&&"symbol"==typeof Symbol.iterator?function(e){return typeof e}:function(e){return e&&"function"==typeof Symbol&&e.constructor===Symbol&&e!==Symbol.prototype?"symbol":typeof e},o(e)}function i(e,t,r,n,o,i,a){try{var s=e[i](a),u=s.value;}catch(e){return void r(e)}s.done?t(u):Promise.resolve(u).then(n,o);}function a(e,t){if(!(e instanceof t))throw new TypeError("Cannot call a class as a function")}function s(e,t){for(var r=0;r<t.length;r++){var o=t[r];o.enumerable=o.enumerable||!1,o.configurable=!0,"value"in o&&(o.writable=!0),Object.defineProperty(e,n(o.key),o);}}function u(e,t,r){return t&&s(e.prototype,t),r&&s(e,r),Object.defineProperty(e,"prototype",{writable:!1}),e}function c(e,t,r){return (t=n(t))in e?Object.defineProperty(e,t,{value:r,enumerable:!0,configurable:!0,writable:!0}):e[t]=r,e}function f(e,t){return h(e)||function(e,t){var r=null==e?null:"undefined"!=typeof Symbol&&e[Symbol.iterator]||e["@@iterator"];if(null!=r){var n,o,i,a,s=[],u=!0,c=!1;try{if(i=(r=r.call(e)).next,0===t){if(Object(r)!==r)return;u=!1;}else for(;!(u=(n=i.call(r)).done)&&(s.push(n.value),s.length!==t);u=!0);}catch(e){c=!0,o=e;}finally{try{if(!u&&null!=r.return&&(a=r.return(),Object(a)!==a))return}finally{if(c)throw o}}return s}}(e,t)||d(e,t)||v()}function l(e){return function(e){if(Array.isArray(e))return y(e)}(e)||p(e)||d(e)||function(){throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}()}function h(e){if(Array.isArray(e))return e}function p(e){if("undefined"!=typeof Symbol&&null!=e[Symbol.iterator]||null!=e["@@iterator"])return Array.from(e)}function d(e,t){if(e){if("string"==typeof e)return y(e,t);var r=Object.prototype.toString.call(e).slice(8,-1);return "Object"===r&&e.constructor&&(r=e.constructor.name),"Map"===r||"Set"===r?Array.from(e):"Arguments"===r||/^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(r)?y(e,t):void 0}}function y(e,t){(null==t||t>e.length)&&(t=e.length);for(var r=0,n=new Array(t);r<t;r++)n[r]=e[r];return n}function v(){throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}function m(e,t){return function(){return e.apply(t,arguments)}}var g,b=Object.prototype.toString,w=Object.getPrototypeOf,E=(g=Object.create(null),function(e){var t=b.call(e);return g[t]||(g[t]=t.slice(8,-1).toLowerCase())}),O=function(e){return e=e.toLowerCase(),function(t){return E(t)===e}},S=function(e){return function(t){return o(t)===e}},j=Array.isArray,R=S("undefined");var A=O("ArrayBuffer");var T=S("string"),x=S("function"),P=S("number"),N=function(e){return null!==e&&"object"===o(e)},k=function(e){if("object"!==E(e))return !1;var t=w(e);return !(null!==t&&t!==Object.prototype&&null!==Object.getPrototypeOf(t)||Symbol.toStringTag in e||Symbol.iterator in e)},_=O("Date"),L=O("File"),C=O("Blob"),F=O("FileList"),U=O("URLSearchParams");function D(e,t){var r,n,i=arguments.length>2&&void 0!==arguments[2]?arguments[2]:{},a=i.allOwnKeys,s=void 0!==a&&a;if(null!=e)if("object"!==o(e)&&(e=[e]),j(e))for(r=0,n=e.length;r<n;r++)t.call(null,e[r],r,e);else {var u,c=s?Object.getOwnPropertyNames(e):Object.keys(e),f=c.length;for(r=0;r<f;r++)u=c[r],t.call(null,e[u],u,e);}}function B(e,t){t=t.toLowerCase();for(var r,n=Object.keys(e),o=n.length;o-- >0;)if(t===(r=n[o]).toLowerCase())return r;return null}var I="undefined"!=typeof globalThis?globalThis:"undefined"!=typeof self?self:"undefined"!=typeof window?window:global,q=function(e){return !R(e)&&e!==I};var z,M=(z="undefined"!=typeof Uint8Array&&w(Uint8Array),function(e){return z&&e instanceof z}),H=O("HTMLFormElement"),J=function(e){var t=Object.prototype.hasOwnProperty;return function(e,r){return t.call(e,r)}}(),G=O("RegExp"),W=function(e,t){var r=Object.getOwnPropertyDescriptors(e),n={};D(r,(function(r,o){var i;!1!==(i=t(r,o,e))&&(n[o]=i||r);})),Object.defineProperties(e,n);},K="abcdefghijklmnopqrstuvwxyz",V="0123456789",X={DIGIT:V,ALPHA:K,ALPHA_DIGIT:K+K.toUpperCase()+V};var $=O("AsyncFunction"),Q={isArray:j,isArrayBuffer:A,isBuffer:function(e){return null!==e&&!R(e)&&null!==e.constructor&&!R(e.constructor)&&x(e.constructor.isBuffer)&&e.constructor.isBuffer(e)},isFormData:function(e){var t;return e&&("function"==typeof FormData&&e instanceof FormData||x(e.append)&&("formdata"===(t=E(e))||"object"===t&&x(e.toString)&&"[object FormData]"===e.toString()))},isArrayBufferView:function(e){return "undefined"!=typeof ArrayBuffer&&ArrayBuffer.isView?ArrayBuffer.isView(e):e&&e.buffer&&A(e.buffer)},isString:T,isNumber:P,isBoolean:function(e){return !0===e||!1===e},isObject:N,isPlainObject:k,isUndefined:R,isDate:_,isFile:L,isBlob:C,isRegExp:G,isFunction:x,isStream:function(e){return N(e)&&x(e.pipe)},isURLSearchParams:U,isTypedArray:M,isFileList:F,forEach:D,merge:function e(){for(var t=q(this)&&this||{},r=t.caseless,n={},o=function(t,o){var i=r&&B(n,o)||o;k(n[i])&&k(t)?n[i]=e(n[i],t):k(t)?n[i]=e({},t):j(t)?n[i]=t.slice():n[i]=t;},i=0,a=arguments.length;i<a;i++)arguments[i]&&D(arguments[i],o);return n},extend:function(e,t,r){var n=arguments.length>3&&void 0!==arguments[3]?arguments[3]:{},o=n.allOwnKeys;return D(t,(function(t,n){r&&x(t)?e[n]=m(t,r):e[n]=t;}),{allOwnKeys:o}),e},trim:function(e){return e.trim?e.trim():e.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,"")},stripBOM:function(e){return 65279===e.charCodeAt(0)&&(e=e.slice(1)),e},inherits:function(e,t,r,n){e.prototype=Object.create(t.prototype,n),e.prototype.constructor=e,Object.defineProperty(e,"super",{value:t.prototype}),r&&Object.assign(e.prototype,r);},toFlatObject:function(e,t,r,n){var o,i,a,s={};if(t=t||{},null==e)return t;do{for(i=(o=Object.getOwnPropertyNames(e)).length;i-- >0;)a=o[i],n&&!n(a,e,t)||s[a]||(t[a]=e[a],s[a]=!0);e=!1!==r&&w(e);}while(e&&(!r||r(e,t))&&e!==Object.prototype);return t},kindOf:E,kindOfTest:O,endsWith:function(e,t,r){e=String(e),(void 0===r||r>e.length)&&(r=e.length),r-=t.length;var n=e.indexOf(t,r);return -1!==n&&n===r},toArray:function(e){if(!e)return null;if(j(e))return e;var t=e.length;if(!P(t))return null;for(var r=new Array(t);t-- >0;)r[t]=e[t];return r},forEachEntry:function(e,t){for(var r,n=(e&&e[Symbol.iterator]).call(e);(r=n.next())&&!r.done;){var o=r.value;t.call(e,o[0],o[1]);}},matchAll:function(e,t){for(var r,n=[];null!==(r=e.exec(t));)n.push(r);return n},isHTMLForm:H,hasOwnProperty:J,hasOwnProp:J,reduceDescriptors:W,freezeMethods:function(e){W(e,(function(t,r){if(x(e)&&-1!==["arguments","caller","callee"].indexOf(r))return !1;var n=e[r];x(n)&&(t.enumerable=!1,"writable"in t?t.writable=!1:t.set||(t.set=function(){throw Error("Can not rewrite read-only method '"+r+"'")}));}));},toObjectSet:function(e,t){var r={},n=function(e){e.forEach((function(e){r[e]=!0;}));};return j(e)?n(e):n(String(e).split(t)),r},toCamelCase:function(e){return e.toLowerCase().replace(/[-_\s]([a-z\d])(\w*)/g,(function(e,t,r){return t.toUpperCase()+r}))},noop:function(){},toFiniteNumber:function(e,t){return e=+e,Number.isFinite(e)?e:t},findKey:B,global:I,isContextDefined:q,ALPHABET:X,generateString:function(){for(var e=arguments.length>0&&void 0!==arguments[0]?arguments[0]:16,t=arguments.length>1&&void 0!==arguments[1]?arguments[1]:X.ALPHA_DIGIT,r="",n=t.length;e--;)r+=t[Math.random()*n|0];return r},isSpecCompliantForm:function(e){return !!(e&&x(e.append)&&"FormData"===e[Symbol.toStringTag]&&e[Symbol.iterator])},toJSONObject:function(e){var t=new Array(10);return function e(r,n){if(N(r)){if(t.indexOf(r)>=0)return;if(!("toJSON"in r)){t[n]=r;var o=j(r)?[]:{};return D(r,(function(t,r){var i=e(t,n+1);!R(i)&&(o[r]=i);})),t[n]=void 0,o}}return r}(e,0)},isAsyncFn:$,isThenable:function(e){return e&&(N(e)||x(e))&&x(e.then)&&x(e.catch)}};function Y(e,t,r,n,o){Error.call(this),Error.captureStackTrace?Error.captureStackTrace(this,this.constructor):this.stack=(new Error).stack,this.message=e,this.name="AxiosError",t&&(this.code=t),r&&(this.config=r),n&&(this.request=n),o&&(this.response=o);}Q.inherits(Y,Error,{toJSON:function(){return {message:this.message,name:this.name,description:this.description,number:this.number,fileName:this.fileName,lineNumber:this.lineNumber,columnNumber:this.columnNumber,stack:this.stack,config:Q.toJSONObject(this.config),code:this.code,status:this.response&&this.response.status?this.response.status:null}}});var Z=Y.prototype,ee={};["ERR_BAD_OPTION_VALUE","ERR_BAD_OPTION","ECONNABORTED","ETIMEDOUT","ERR_NETWORK","ERR_FR_TOO_MANY_REDIRECTS","ERR_DEPRECATED","ERR_BAD_RESPONSE","ERR_BAD_REQUEST","ERR_CANCELED","ERR_NOT_SUPPORT","ERR_INVALID_URL"].forEach((function(e){ee[e]={value:e};})),Object.defineProperties(Y,ee),Object.defineProperty(Z,"isAxiosError",{value:!0}),Y.from=function(e,t,r,n,o,i){var a=Object.create(Z);return Q.toFlatObject(e,a,(function(e){return e!==Error.prototype}),(function(e){return "isAxiosError"!==e})),Y.call(a,e.message,t,r,n,o),a.cause=e,a.name=e.name,i&&Object.assign(a,i),a};function te(e){return Q.isPlainObject(e)||Q.isArray(e)}function re(e){return Q.endsWith(e,"[]")?e.slice(0,-2):e}function ne(e,t,r){return e?e.concat(t).map((function(e,t){return e=re(e),!r&&t?"["+e+"]":e})).join(r?".":""):t}var oe=Q.toFlatObject(Q,{},null,(function(e){return /^is[A-Z]/.test(e)}));function ie(e,t,r){if(!Q.isObject(e))throw new TypeError("target must be an object");t=t||new FormData;var n=(r=Q.toFlatObject(r,{metaTokens:!0,dots:!1,indexes:!1},!1,(function(e,t){return !Q.isUndefined(t[e])}))).metaTokens,i=r.visitor||f,a=r.dots,s=r.indexes,u=(r.Blob||"undefined"!=typeof Blob&&Blob)&&Q.isSpecCompliantForm(t);if(!Q.isFunction(i))throw new TypeError("visitor must be a function");function c(e){if(null===e)return "";if(Q.isDate(e))return e.toISOString();if(!u&&Q.isBlob(e))throw new Y("Blob is not supported. Use a Buffer instead.");return Q.isArrayBuffer(e)||Q.isTypedArray(e)?u&&"function"==typeof Blob?new Blob([e]):Buffer.from(e):e}function f(e,r,i){var u=e;if(e&&!i&&"object"===o(e))if(Q.endsWith(r,"{}"))r=n?r:r.slice(0,-2),e=JSON.stringify(e);else if(Q.isArray(e)&&function(e){return Q.isArray(e)&&!e.some(te)}(e)||(Q.isFileList(e)||Q.endsWith(r,"[]"))&&(u=Q.toArray(e)))return r=re(r),u.forEach((function(e,n){!Q.isUndefined(e)&&null!==e&&t.append(!0===s?ne([r],n,a):null===s?r:r+"[]",c(e));})),!1;return !!te(e)||(t.append(ne(i,r,a),c(e)),!1)}var l=[],h=Object.assign(oe,{defaultVisitor:f,convertValue:c,isVisitable:te});if(!Q.isObject(e))throw new TypeError("data must be an object");return function e(r,n){if(!Q.isUndefined(r)){if(-1!==l.indexOf(r))throw Error("Circular reference detected in "+n.join("."));l.push(r),Q.forEach(r,(function(r,o){!0===(!(Q.isUndefined(r)||null===r)&&i.call(t,r,Q.isString(o)?o.trim():o,n,h))&&e(r,n?n.concat(o):[o]);})),l.pop();}}(e),t}function ae(e){var t={"!":"%21","'":"%27","(":"%28",")":"%29","~":"%7E","%20":"+","%00":"\0"};return encodeURIComponent(e).replace(/[!'()~]|%20|%00/g,(function(e){return t[e]}))}function se(e,t){this._pairs=[],e&&ie(e,this,t);}var ue=se.prototype;function ce(e){return encodeURIComponent(e).replace(/%3A/gi,":").replace(/%24/g,"$").replace(/%2C/gi,",").replace(/%20/g,"+").replace(/%5B/gi,"[").replace(/%5D/gi,"]")}function fe(e,t,r){if(!t)return e;var n,o=r&&r.encode||ce,i=r&&r.serialize;if(n=i?i(t,r):Q.isURLSearchParams(t)?t.toString():new se(t,r).toString(o)){var a=e.indexOf("#");-1!==a&&(e=e.slice(0,a)),e+=(-1===e.indexOf("?")?"?":"&")+n;}return e}ue.append=function(e,t){this._pairs.push([e,t]);},ue.toString=function(e){var t=e?function(t){return e.call(this,t,ae)}:ae;return this._pairs.map((function(e){return t(e[0])+"="+t(e[1])}),"").join("&")};var le,he=function(){function e(){a(this,e),this.handlers=[];}return u(e,[{key:"use",value:function(e,t,r){return this.handlers.push({fulfilled:e,rejected:t,synchronous:!!r&&r.synchronous,runWhen:r?r.runWhen:null}),this.handlers.length-1}},{key:"eject",value:function(e){this.handlers[e]&&(this.handlers[e]=null);}},{key:"clear",value:function(){this.handlers&&(this.handlers=[]);}},{key:"forEach",value:function(e){Q.forEach(this.handlers,(function(t){null!==t&&e(t);}));}}]),e}(),pe={silentJSONParsing:!0,forcedJSONParsing:!0,clarifyTimeoutError:!1},de={isBrowser:!0,classes:{URLSearchParams:"undefined"!=typeof URLSearchParams?URLSearchParams:se,FormData:"undefined"!=typeof FormData?FormData:null,Blob:"undefined"!=typeof Blob?Blob:null},protocols:["http","https","file","blob","url","data"]},ye="undefined"!=typeof window&&"undefined"!=typeof document,ve=(le="undefined"!=typeof navigator&&navigator.product,ye&&["ReactNative","NativeScript","NS"].indexOf(le)<0),me="undefined"!=typeof WorkerGlobalScope&&self instanceof WorkerGlobalScope&&"function"==typeof self.importScripts,ge=t(t({},Object.freeze({__proto__:null,hasBrowserEnv:ye,hasStandardBrowserWebWorkerEnv:me,hasStandardBrowserEnv:ve})),de);function be(e){function t(e,r,n,o){var i=e[o++];if("__proto__"===i)return !0;var a=Number.isFinite(+i),s=o>=e.length;return i=!i&&Q.isArray(n)?n.length:i,s?(Q.hasOwnProp(n,i)?n[i]=[n[i],r]:n[i]=r,!a):(n[i]&&Q.isObject(n[i])||(n[i]=[]),t(e,r,n[i],o)&&Q.isArray(n[i])&&(n[i]=function(e){var t,r,n={},o=Object.keys(e),i=o.length;for(t=0;t<i;t++)n[r=o[t]]=e[r];return n}(n[i])),!a)}if(Q.isFormData(e)&&Q.isFunction(e.entries)){var r={};return Q.forEachEntry(e,(function(e,n){t(function(e){return Q.matchAll(/\w+|\[(\w*)]/g,e).map((function(e){return "[]"===e[0]?"":e[1]||e[0]}))}(e),n,r,0);})),r}return null}var we={transitional:pe,adapter:["xhr","http"],transformRequest:[function(e,t){var r,n=t.getContentType()||"",o=n.indexOf("application/json")>-1,i=Q.isObject(e);if(i&&Q.isHTMLForm(e)&&(e=new FormData(e)),Q.isFormData(e))return o?JSON.stringify(be(e)):e;if(Q.isArrayBuffer(e)||Q.isBuffer(e)||Q.isStream(e)||Q.isFile(e)||Q.isBlob(e))return e;if(Q.isArrayBufferView(e))return e.buffer;if(Q.isURLSearchParams(e))return t.setContentType("application/x-www-form-urlencoded;charset=utf-8",!1),e.toString();if(i){if(n.indexOf("application/x-www-form-urlencoded")>-1)return function(e,t){return ie(e,new ge.classes.URLSearchParams,Object.assign({visitor:function(e,t,r,n){return ge.isNode&&Q.isBuffer(e)?(this.append(t,e.toString("base64")),!1):n.defaultVisitor.apply(this,arguments)}},t))}(e,this.formSerializer).toString();if((r=Q.isFileList(e))||n.indexOf("multipart/form-data")>-1){var a=this.env&&this.env.FormData;return ie(r?{"files[]":e}:e,a&&new a,this.formSerializer)}}return i||o?(t.setContentType("application/json",!1),function(e,t,r){if(Q.isString(e))try{return (t||JSON.parse)(e),Q.trim(e)}catch(e){if("SyntaxError"!==e.name)throw e}return (r||JSON.stringify)(e)}(e)):e}],transformResponse:[function(e){var t=this.transitional||we.transitional,r=t&&t.forcedJSONParsing,n="json"===this.responseType;if(e&&Q.isString(e)&&(r&&!this.responseType||n)){var o=!(t&&t.silentJSONParsing)&&n;try{return JSON.parse(e)}catch(e){if(o){if("SyntaxError"===e.name)throw Y.from(e,Y.ERR_BAD_RESPONSE,this,null,this.response);throw e}}}return e}],timeout:0,xsrfCookieName:"XSRF-TOKEN",xsrfHeaderName:"X-XSRF-TOKEN",maxContentLength:-1,maxBodyLength:-1,env:{FormData:ge.classes.FormData,Blob:ge.classes.Blob},validateStatus:function(e){return e>=200&&e<300},headers:{common:{Accept:"application/json, text/plain, */*","Content-Type":void 0}}};Q.forEach(["delete","get","head","post","put","patch"],(function(e){we.headers[e]={};}));var Ee=we,Oe=Q.toObjectSet(["age","authorization","content-length","content-type","etag","expires","from","host","if-modified-since","if-unmodified-since","last-modified","location","max-forwards","proxy-authorization","referer","retry-after","user-agent"]),Se=Symbol("internals");function je(e){return e&&String(e).trim().toLowerCase()}function Re(e){return !1===e||null==e?e:Q.isArray(e)?e.map(Re):String(e)}function Ae(e,t,r,n,o){return Q.isFunction(n)?n.call(this,t,r):(o&&(t=r),Q.isString(t)?Q.isString(n)?-1!==t.indexOf(n):Q.isRegExp(n)?n.test(t):void 0:void 0)}var Te=function(e,t){function r(e){a(this,r),e&&this.set(e);}return u(r,[{key:"set",value:function(e,t,r){var n=this;function o(e,t,r){var o=je(t);if(!o)throw new Error("header name must be a non-empty string");var i=Q.findKey(n,o);(!i||void 0===n[i]||!0===r||void 0===r&&!1!==n[i])&&(n[i||t]=Re(e));}var i,a,s,u,c,f=function(e,t){return Q.forEach(e,(function(e,r){return o(e,r,t)}))};return Q.isPlainObject(e)||e instanceof this.constructor?f(e,t):Q.isString(e)&&(e=e.trim())&&!/^[-_a-zA-Z0-9^`|~,!#$%&'*+.]+$/.test(e.trim())?f((c={},(i=e)&&i.split("\n").forEach((function(e){u=e.indexOf(":"),a=e.substring(0,u).trim().toLowerCase(),s=e.substring(u+1).trim(),!a||c[a]&&Oe[a]||("set-cookie"===a?c[a]?c[a].push(s):c[a]=[s]:c[a]=c[a]?c[a]+", "+s:s);})),c),t):null!=e&&o(t,e,r),this}},{key:"get",value:function(e,t){if(e=je(e)){var r=Q.findKey(this,e);if(r){var n=this[r];if(!t)return n;if(!0===t)return function(e){for(var t,r=Object.create(null),n=/([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;t=n.exec(e);)r[t[1]]=t[2];return r}(n);if(Q.isFunction(t))return t.call(this,n,r);if(Q.isRegExp(t))return t.exec(n);throw new TypeError("parser must be boolean|regexp|function")}}}},{key:"has",value:function(e,t){if(e=je(e)){var r=Q.findKey(this,e);return !(!r||void 0===this[r]||t&&!Ae(0,this[r],r,t))}return !1}},{key:"delete",value:function(e,t){var r=this,n=!1;function o(e){if(e=je(e)){var o=Q.findKey(r,e);!o||t&&!Ae(0,r[o],o,t)||(delete r[o],n=!0);}}return Q.isArray(e)?e.forEach(o):o(e),n}},{key:"clear",value:function(e){for(var t=Object.keys(this),r=t.length,n=!1;r--;){var o=t[r];e&&!Ae(0,this[o],o,e,!0)||(delete this[o],n=!0);}return n}},{key:"normalize",value:function(e){var t=this,r={};return Q.forEach(this,(function(n,o){var i=Q.findKey(r,o);if(i)return t[i]=Re(n),void delete t[o];var a=e?function(e){return e.trim().toLowerCase().replace(/([a-z\d])(\w*)/g,(function(e,t,r){return t.toUpperCase()+r}))}(o):String(o).trim();a!==o&&delete t[o],t[a]=Re(n),r[a]=!0;})),this}},{key:"concat",value:function(){for(var e,t=arguments.length,r=new Array(t),n=0;n<t;n++)r[n]=arguments[n];return (e=this.constructor).concat.apply(e,[this].concat(r))}},{key:"toJSON",value:function(e){var t=Object.create(null);return Q.forEach(this,(function(r,n){null!=r&&!1!==r&&(t[n]=e&&Q.isArray(r)?r.join(", "):r);})),t}},{key:Symbol.iterator,value:function(){return Object.entries(this.toJSON())[Symbol.iterator]()}},{key:"toString",value:function(){return Object.entries(this.toJSON()).map((function(e){var t=f(e,2);return t[0]+": "+t[1]})).join("\n")}},{key:Symbol.toStringTag,get:function(){return "AxiosHeaders"}}],[{key:"from",value:function(e){return e instanceof this?e:new this(e)}},{key:"concat",value:function(e){for(var t=new this(e),r=arguments.length,n=new Array(r>1?r-1:0),o=1;o<r;o++)n[o-1]=arguments[o];return n.forEach((function(e){return t.set(e)})),t}},{key:"accessor",value:function(e){var t=(this[Se]=this[Se]={accessors:{}}).accessors,r=this.prototype;function n(e){var n=je(e);t[n]||(!function(e,t){var r=Q.toCamelCase(" "+t);["get","set","has"].forEach((function(n){Object.defineProperty(e,n+r,{value:function(e,r,o){return this[n].call(this,t,e,r,o)},configurable:!0});}));}(r,e),t[n]=!0);}return Q.isArray(e)?e.forEach(n):n(e),this}}]),r}();Te.accessor(["Content-Type","Content-Length","Accept","Accept-Encoding","User-Agent","Authorization"]),Q.reduceDescriptors(Te.prototype,(function(e,t){var r=e.value,n=t[0].toUpperCase()+t.slice(1);return {get:function(){return r},set:function(e){this[n]=e;}}})),Q.freezeMethods(Te);var xe=Te;function Pe(e,t){var r=this||Ee,n=t||r,o=xe.from(n.headers),i=n.data;return Q.forEach(e,(function(e){i=e.call(r,i,o.normalize(),t?t.status:void 0);})),o.normalize(),i}function Ne(e){return !(!e||!e.__CANCEL__)}function ke(e,t,r){Y.call(this,null==e?"canceled":e,Y.ERR_CANCELED,t,r),this.name="CanceledError";}Q.inherits(ke,Y,{__CANCEL__:!0});var _e=ge.hasStandardBrowserEnv?{write:function(e,t,r,n,o,i){var a=[e+"="+encodeURIComponent(t)];Q.isNumber(r)&&a.push("expires="+new Date(r).toGMTString()),Q.isString(n)&&a.push("path="+n),Q.isString(o)&&a.push("domain="+o),!0===i&&a.push("secure"),document.cookie=a.join("; ");},read:function(e){var t=document.cookie.match(new RegExp("(^|;\\s*)("+e+")=([^;]*)"));return t?decodeURIComponent(t[3]):null},remove:function(e){this.write(e,"",Date.now()-864e5);}}:{write:function(){},read:function(){return null},remove:function(){}};function Le(e,t){return e&&!/^([a-z][a-z\d+\-.]*:)?\/\//i.test(t)?function(e,t){return t?e.replace(/\/?\/$/,"")+"/"+t.replace(/^\/+/,""):e}(e,t):t}var Ce=ge.hasStandardBrowserEnv?function(){var e,t=/(msie|trident)/i.test(navigator.userAgent),r=document.createElement("a");function n(e){var n=e;return t&&(r.setAttribute("href",n),n=r.href),r.setAttribute("href",n),{href:r.href,protocol:r.protocol?r.protocol.replace(/:$/,""):"",host:r.host,search:r.search?r.search.replace(/^\?/,""):"",hash:r.hash?r.hash.replace(/^#/,""):"",hostname:r.hostname,port:r.port,pathname:"/"===r.pathname.charAt(0)?r.pathname:"/"+r.pathname}}return e=n(window.location.href),function(t){var r=Q.isString(t)?n(t):t;return r.protocol===e.protocol&&r.host===e.host}}():function(){return !0};function Fe(e,t){var r=0,n=function(e,t){e=e||10;var r,n=new Array(e),o=new Array(e),i=0,a=0;return t=void 0!==t?t:1e3,function(s){var u=Date.now(),c=o[a];r||(r=u),n[i]=s,o[i]=u;for(var f=a,l=0;f!==i;)l+=n[f++],f%=e;if((i=(i+1)%e)===a&&(a=(a+1)%e),!(u-r<t)){var h=c&&u-c;return h?Math.round(1e3*l/h):void 0}}}(50,250);return function(o){var i=o.loaded,a=o.lengthComputable?o.total:void 0,s=i-r,u=n(s);r=i;var c={loaded:i,total:a,progress:a?i/a:void 0,bytes:s,rate:u||void 0,estimated:u&&a&&i<=a?(a-i)/u:void 0,event:o};c[t?"download":"upload"]=!0,e(c);}}var Ue={http:null,xhr:"undefined"!=typeof XMLHttpRequest&&function(e){return new Promise((function(t,r){var n,o,i,a=e.data,s=xe.from(e.headers).normalize(),u=e.responseType,c=e.withXSRFToken;function f(){e.cancelToken&&e.cancelToken.unsubscribe(n),e.signal&&e.signal.removeEventListener("abort",n);}if(Q.isFormData(a))if(ge.hasStandardBrowserEnv||ge.hasStandardBrowserWebWorkerEnv)s.setContentType(!1);else if(!1!==(o=s.getContentType())){var y=o?o.split(";").map((function(e){return e.trim()})).filter(Boolean):[],m=h(i=y)||p(i)||d(i)||v(),g=m[0],b=m.slice(1);s.setContentType([g||"multipart/form-data"].concat(l(b)).join("; "));}var w=new XMLHttpRequest;if(e.auth){var E=e.auth.username||"",O=e.auth.password?unescape(encodeURIComponent(e.auth.password)):"";s.set("Authorization","Basic "+btoa(E+":"+O));}var S=Le(e.baseURL,e.url);function j(){if(w){var n=xe.from("getAllResponseHeaders"in w&&w.getAllResponseHeaders());!function(e,t,r){var n=r.config.validateStatus;r.status&&n&&!n(r.status)?t(new Y("Request failed with status code "+r.status,[Y.ERR_BAD_REQUEST,Y.ERR_BAD_RESPONSE][Math.floor(r.status/100)-4],r.config,r.request,r)):e(r);}((function(e){t(e),f();}),(function(e){r(e),f();}),{data:u&&"text"!==u&&"json"!==u?w.response:w.responseText,status:w.status,statusText:w.statusText,headers:n,config:e,request:w}),w=null;}}if(w.open(e.method.toUpperCase(),fe(S,e.params,e.paramsSerializer),!0),w.timeout=e.timeout,"onloadend"in w?w.onloadend=j:w.onreadystatechange=function(){w&&4===w.readyState&&(0!==w.status||w.responseURL&&0===w.responseURL.indexOf("file:"))&&setTimeout(j);},w.onabort=function(){w&&(r(new Y("Request aborted",Y.ECONNABORTED,e,w)),w=null);},w.onerror=function(){r(new Y("Network Error",Y.ERR_NETWORK,e,w)),w=null;},w.ontimeout=function(){var t=e.timeout?"timeout of "+e.timeout+"ms exceeded":"timeout exceeded",n=e.transitional||pe;e.timeoutErrorMessage&&(t=e.timeoutErrorMessage),r(new Y(t,n.clarifyTimeoutError?Y.ETIMEDOUT:Y.ECONNABORTED,e,w)),w=null;},ge.hasStandardBrowserEnv&&(c&&Q.isFunction(c)&&(c=c(e)),c||!1!==c&&Ce(S))){var R=e.xsrfHeaderName&&e.xsrfCookieName&&_e.read(e.xsrfCookieName);R&&s.set(e.xsrfHeaderName,R);}void 0===a&&s.setContentType(null),"setRequestHeader"in w&&Q.forEach(s.toJSON(),(function(e,t){w.setRequestHeader(t,e);})),Q.isUndefined(e.withCredentials)||(w.withCredentials=!!e.withCredentials),u&&"json"!==u&&(w.responseType=e.responseType),"function"==typeof e.onDownloadProgress&&w.addEventListener("progress",Fe(e.onDownloadProgress,!0)),"function"==typeof e.onUploadProgress&&w.upload&&w.upload.addEventListener("progress",Fe(e.onUploadProgress)),(e.cancelToken||e.signal)&&(n=function(t){w&&(r(!t||t.type?new ke(null,e,w):t),w.abort(),w=null);},e.cancelToken&&e.cancelToken.subscribe(n),e.signal&&(e.signal.aborted?n():e.signal.addEventListener("abort",n)));var A,T=(A=/^([-+\w]{1,25})(:?\/\/|:)/.exec(S))&&A[1]||"";T&&-1===ge.protocols.indexOf(T)?r(new Y("Unsupported protocol "+T+":",Y.ERR_BAD_REQUEST,e)):w.send(a||null);}))}};Q.forEach(Ue,(function(e,t){if(e){try{Object.defineProperty(e,"name",{value:t});}catch(e){}Object.defineProperty(e,"adapterName",{value:t});}}));var De=function(e){return "- ".concat(e)},Be=function(e){return Q.isFunction(e)||null===e||!1===e},Ie=function(e){for(var t,r,n=(e=Q.isArray(e)?e:[e]).length,o={},i=0;i<n;i++){var a=void 0;if(r=t=e[i],!Be(t)&&void 0===(r=Ue[(a=String(t)).toLowerCase()]))throw new Y("Unknown adapter '".concat(a,"'"));if(r)break;o[a||"#"+i]=r;}if(!r){var s=Object.entries(o).map((function(e){var t=f(e,2),r=t[0],n=t[1];return "adapter ".concat(r," ")+(!1===n?"is not supported by the environment":"is not available in the build")}));throw new Y("There is no suitable adapter to dispatch the request "+(n?s.length>1?"since :\n"+s.map(De).join("\n"):" "+De(s[0]):"as no adapter specified"),"ERR_NOT_SUPPORT")}return r};function qe(e){if(e.cancelToken&&e.cancelToken.throwIfRequested(),e.signal&&e.signal.aborted)throw new ke(null,e)}function ze(e){return qe(e),e.headers=xe.from(e.headers),e.data=Pe.call(e,e.transformRequest),-1!==["post","put","patch"].indexOf(e.method)&&e.headers.setContentType("application/x-www-form-urlencoded",!1),Ie(e.adapter||Ee.adapter)(e).then((function(t){return qe(e),t.data=Pe.call(e,e.transformResponse,t),t.headers=xe.from(t.headers),t}),(function(t){return Ne(t)||(qe(e),t&&t.response&&(t.response.data=Pe.call(e,e.transformResponse,t.response),t.response.headers=xe.from(t.response.headers))),Promise.reject(t)}))}var Me=function(e){return e instanceof xe?t({},e):e};function He(e,t){t=t||{};var r={};function n(e,t,r){return Q.isPlainObject(e)&&Q.isPlainObject(t)?Q.merge.call({caseless:r},e,t):Q.isPlainObject(t)?Q.merge({},t):Q.isArray(t)?t.slice():t}function o(e,t,r){return Q.isUndefined(t)?Q.isUndefined(e)?void 0:n(void 0,e,r):n(e,t,r)}function i(e,t){if(!Q.isUndefined(t))return n(void 0,t)}function a(e,t){return Q.isUndefined(t)?Q.isUndefined(e)?void 0:n(void 0,e):n(void 0,t)}function s(r,o,i){return i in t?n(r,o):i in e?n(void 0,r):void 0}var u={url:i,method:i,data:i,baseURL:a,transformRequest:a,transformResponse:a,paramsSerializer:a,timeout:a,timeoutMessage:a,withCredentials:a,withXSRFToken:a,adapter:a,responseType:a,xsrfCookieName:a,xsrfHeaderName:a,onUploadProgress:a,onDownloadProgress:a,decompress:a,maxContentLength:a,maxBodyLength:a,beforeRedirect:a,transport:a,httpAgent:a,httpsAgent:a,cancelToken:a,socketPath:a,responseEncoding:a,validateStatus:s,headers:function(e,t){return o(Me(e),Me(t),!0)}};return Q.forEach(Object.keys(Object.assign({},e,t)),(function(n){var i=u[n]||o,a=i(e[n],t[n],n);Q.isUndefined(a)&&i!==s||(r[n]=a);})),r}var Je="1.6.8",Ge={};["object","boolean","number","function","string","symbol"].forEach((function(e,t){Ge[e]=function(r){return o(r)===e||"a"+(t<1?"n ":" ")+e};}));var We={};Ge.transitional=function(e,t,r){function n(e,t){return "[Axios v1.6.8] Transitional option '"+e+"'"+t+(r?". "+r:"")}return function(r,o,i){if(!1===e)throw new Y(n(o," has been removed"+(t?" in "+t:"")),Y.ERR_DEPRECATED);return t&&!We[o]&&(We[o]=!0,console.warn(n(o," has been deprecated since v"+t+" and will be removed in the near future"))),!e||e(r,o,i)}};var Ke={assertOptions:function(e,t,r){if("object"!==o(e))throw new Y("options must be an object",Y.ERR_BAD_OPTION_VALUE);for(var n=Object.keys(e),i=n.length;i-- >0;){var a=n[i],s=t[a];if(s){var u=e[a],c=void 0===u||s(u,a,e);if(!0!==c)throw new Y("option "+a+" must be "+c,Y.ERR_BAD_OPTION_VALUE)}else if(!0!==r)throw new Y("Unknown option "+a,Y.ERR_BAD_OPTION)}},validators:Ge},Ve=Ke.validators,Xe=function(){function e(t){a(this,e),this.defaults=t,this.interceptors={request:new he,response:new he};}var t,n;return u(e,[{key:"request",value:(t=r().mark((function e(t,n){var o,i;return r().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return e.prev=0,e.next=3,this._request(t,n);case 3:return e.abrupt("return",e.sent);case 6:throw e.prev=6,e.t0=e.catch(0),e.t0 instanceof Error&&(Error.captureStackTrace?Error.captureStackTrace(o={}):o=new Error,i=o.stack?o.stack.replace(/^.+\n/,""):"",e.t0.stack?i&&!String(e.t0.stack).endsWith(i.replace(/^.+\n.+\n/,""))&&(e.t0.stack+="\n"+i):e.t0.stack=i),e.t0;case 10:case"end":return e.stop()}}),e,this,[[0,6]])})),n=function(){var e=this,r=arguments;return new Promise((function(n,o){var a=t.apply(e,r);function s(e){i(a,n,o,s,u,"next",e);}function u(e){i(a,n,o,s,u,"throw",e);}s(void 0);}))},function(e,t){return n.apply(this,arguments)})},{key:"_request",value:function(e,t){"string"==typeof e?(t=t||{}).url=e:t=e||{};var r=t=He(this.defaults,t),n=r.transitional,o=r.paramsSerializer,i=r.headers;void 0!==n&&Ke.assertOptions(n,{silentJSONParsing:Ve.transitional(Ve.boolean),forcedJSONParsing:Ve.transitional(Ve.boolean),clarifyTimeoutError:Ve.transitional(Ve.boolean)},!1),null!=o&&(Q.isFunction(o)?t.paramsSerializer={serialize:o}:Ke.assertOptions(o,{encode:Ve.function,serialize:Ve.function},!0)),t.method=(t.method||this.defaults.method||"get").toLowerCase();var a=i&&Q.merge(i.common,i[t.method]);i&&Q.forEach(["delete","get","head","post","put","patch","common"],(function(e){delete i[e];})),t.headers=xe.concat(a,i);var s=[],u=!0;this.interceptors.request.forEach((function(e){"function"==typeof e.runWhen&&!1===e.runWhen(t)||(u=u&&e.synchronous,s.unshift(e.fulfilled,e.rejected));}));var c,f=[];this.interceptors.response.forEach((function(e){f.push(e.fulfilled,e.rejected);}));var l,h=0;if(!u){var p=[ze.bind(this),void 0];for(p.unshift.apply(p,s),p.push.apply(p,f),l=p.length,c=Promise.resolve(t);h<l;)c=c.then(p[h++],p[h++]);return c}l=s.length;var d=t;for(h=0;h<l;){var y=s[h++],v=s[h++];try{d=y(d);}catch(e){v.call(this,e);break}}try{c=ze.call(this,d);}catch(e){return Promise.reject(e)}for(h=0,l=f.length;h<l;)c=c.then(f[h++],f[h++]);return c}},{key:"getUri",value:function(e){return fe(Le((e=He(this.defaults,e)).baseURL,e.url),e.params,e.paramsSerializer)}}]),e}();Q.forEach(["delete","get","head","options"],(function(e){Xe.prototype[e]=function(t,r){return this.request(He(r||{},{method:e,url:t,data:(r||{}).data}))};})),Q.forEach(["post","put","patch"],(function(e){function t(t){return function(r,n,o){return this.request(He(o||{},{method:e,headers:t?{"Content-Type":"multipart/form-data"}:{},url:r,data:n}))}}Xe.prototype[e]=t(),Xe.prototype[e+"Form"]=t(!0);}));var $e=Xe,Qe=function(){function e(t){if(a(this,e),"function"!=typeof t)throw new TypeError("executor must be a function.");var r;this.promise=new Promise((function(e){r=e;}));var n=this;this.promise.then((function(e){if(n._listeners){for(var t=n._listeners.length;t-- >0;)n._listeners[t](e);n._listeners=null;}})),this.promise.then=function(e){var t,r=new Promise((function(e){n.subscribe(e),t=e;})).then(e);return r.cancel=function(){n.unsubscribe(t);},r},t((function(e,t,o){n.reason||(n.reason=new ke(e,t,o),r(n.reason));}));}return u(e,[{key:"throwIfRequested",value:function(){if(this.reason)throw this.reason}},{key:"subscribe",value:function(e){this.reason?e(this.reason):this._listeners?this._listeners.push(e):this._listeners=[e];}},{key:"unsubscribe",value:function(e){if(this._listeners){var t=this._listeners.indexOf(e);-1!==t&&this._listeners.splice(t,1);}}}],[{key:"source",value:function(){var t;return {token:new e((function(e){t=e;})),cancel:t}}}]),e}();var Ye={Continue:100,SwitchingProtocols:101,Processing:102,EarlyHints:103,Ok:200,Created:201,Accepted:202,NonAuthoritativeInformation:203,NoContent:204,ResetContent:205,PartialContent:206,MultiStatus:207,AlreadyReported:208,ImUsed:226,MultipleChoices:300,MovedPermanently:301,Found:302,SeeOther:303,NotModified:304,UseProxy:305,Unused:306,TemporaryRedirect:307,PermanentRedirect:308,BadRequest:400,Unauthorized:401,PaymentRequired:402,Forbidden:403,NotFound:404,MethodNotAllowed:405,NotAcceptable:406,ProxyAuthenticationRequired:407,RequestTimeout:408,Conflict:409,Gone:410,LengthRequired:411,PreconditionFailed:412,PayloadTooLarge:413,UriTooLong:414,UnsupportedMediaType:415,RangeNotSatisfiable:416,ExpectationFailed:417,ImATeapot:418,MisdirectedRequest:421,UnprocessableEntity:422,Locked:423,FailedDependency:424,TooEarly:425,UpgradeRequired:426,PreconditionRequired:428,TooManyRequests:429,RequestHeaderFieldsTooLarge:431,UnavailableForLegalReasons:451,InternalServerError:500,NotImplemented:501,BadGateway:502,ServiceUnavailable:503,GatewayTimeout:504,HttpVersionNotSupported:505,VariantAlsoNegotiates:506,InsufficientStorage:507,LoopDetected:508,NotExtended:510,NetworkAuthenticationRequired:511};Object.entries(Ye).forEach((function(e){var t=f(e,2),r=t[0],n=t[1];Ye[n]=r;}));var Ze=Ye;var et=function e(t){var r=new $e(t),n=m($e.prototype.request,r);return Q.extend(n,$e.prototype,r,{allOwnKeys:!0}),Q.extend(n,r,null,{allOwnKeys:!0}),n.create=function(r){return e(He(t,r))},n}(Ee);return et.Axios=$e,et.CanceledError=ke,et.CancelToken=Qe,et.isCancel=Ne,et.VERSION=Je,et.toFormData=ie,et.AxiosError=Y,et.Cancel=et.CanceledError,et.all=function(e){return Promise.all(e)},et.spread=function(e){return function(t){return e.apply(null,t)}},et.isAxiosError=function(e){return Q.isObject(e)&&!0===e.isAxiosError},et.mergeConfig=He,et.AxiosHeaders=xe,et.formToJSON=function(e){return be(Q.isHTMLForm(e)?new FormData(e):e)},et.getAdapter=Ie,et.HttpStatusCode=Ze,et.default=et,et}));





var axios = module.exports;

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
      // Allow provider without '@': "provider:prefix:name"
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

const defaultIconDimensions = Object.freeze(
  {
    left: 0,
    top: 0,
    width: 16,
    height: 16
  }
);
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
    currentProps = mergeIconData(
      icons[name2] || aliases[name2],
      currentProps
    );
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
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(
      icon,
      defaultExtendedIconProps
    )) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(
      icon,
      defaultExtendedIconProps
    )) {
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
function addIconSet(storage, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage.icons[name] = icon;
    } else {
      storage.missing.add(name);
    }
  });
}
function addIconToStorage(storage, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage.icons[name] = { ...icon };
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
    const storage = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage.icons[iconName] || (storage.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage, icon.name, data);
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
  const storage = getStorage(provider, prefix);
  return !!addIconSet(storage, data);
}

const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  // Dimensions
  ...defaultIconSizeCustomisations,
  // Transformations
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

function splitSVGDefs(content, tag = "defs") {
  let defs = "";
  const index = content.indexOf("<" + tag);
  while (index >= 0) {
    const start = content.indexOf(">", index);
    const end = content.indexOf("</" + tag);
    if (start === -1 || end === -1) {
      break;
    }
    const endEnd = content.indexOf(">", end);
    if (endEnd === -1) {
      break;
    }
    defs += content.slice(start + 1, end).trim();
    content = content.slice(0, index).trim() + content.slice(endEnd + 1);
  }
  return {
    defs,
    content
  };
}
function mergeDefsAndContent(defs, content) {
  return defs ? "<defs>" + defs + "</defs>" + content : content;
}
function wrapSVGContent(body, start, end) {
  const split = splitSVGDefs(body);
  return mergeDefsAndContent(split.defs, start + split.content + end);
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
        transformations.push(
          "translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")"
        );
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push(
        "translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")"
      );
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
        transformations.unshift(
          "rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")"
        );
        break;
      case 2:
        transformations.unshift(
          "rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")"
        );
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift(
          "rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")"
        );
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
      body = wrapSVGContent(
        body,
        '<g transform="' + transformations.join(" ") + '">',
        "</g>"
      );
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
  const viewBox = [box.left, box.top, boxWidth, boxHeight];
  attributes.viewBox = viewBox.join(" ");
  return {
    attributes,
    viewBox,
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
    body = body.replace(
      // Allowed characters before id: [#;"]
      // Allowed characters after id: [)"], .[a-z]
      new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"),
      "$1" + newID + suffix + "$3"
    );
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
    // API hosts
    resources,
    // Root path
    path: source.path || "/",
    // URL length limit
    maxURL: source.maxURL || 500,
    // Timeout before next host is used.
    rotate: source.rotate || 750,
    // Timeout before failing query.
    timeout: source.timeout || 5e3,
    // Randomise default API end point.
    random: source.random === true,
    // Start index
    index: source.index || 0,
    // Receive data after time out (used if time out kicks in first, then API module sends data anyway).
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
  const storage = /* @__PURE__ */ Object.create(null);
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
    const providerStorage = storage[provider] || (storage[provider] = /* @__PURE__ */ Object.create(null));
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
  storages.forEach((storage) => {
    const items = storage.loaderCallbacks;
    if (items) {
      storage.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage) {
  if (!storage.pendingCallbacksFlag) {
    storage.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage.pendingCallbacksFlag = false;
      const items = storage.loaderCallbacks ? storage.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage.provider;
      const prefix = storage.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage.missing.has(name)) {
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
            removeCallback([storage], item.id);
          }
          item.callback(
            icons.loaded.slice(0),
            icons.missing.slice(0),
            icons.pending.slice(0),
            item.abort
          );
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
  pendingSources.forEach((storage) => {
    (storage.loaderCallbacks || (storage.loaderCallbacks = [])).push(item);
  });
  return abort;
}

function listToIcons(list, validate = true, simpleNames = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}

// src/config.ts
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};

// src/query.ts
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

// src/index.ts
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
    const query2 = sendQuery(
      config,
      payload,
      queryCallback,
      (data, error) => {
        cleanup();
        if (doneCallback) {
          doneCallback(data, error);
        }
      }
    );
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
  let send;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send = api.send;
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
        send = api.send;
      }
    }
  }
  if (!redundancy || !send) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send, callback)().abort;
}

const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
const browserStorageLimit = 50;

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

function setBrowserStorageItemsCount(storage, value) {
  return setStoredItem(storage, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage) {
  return parseInt(getStoredItem(storage, browserCacheCountKey)) || 0;
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
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && // Valid item: run callback
      callback(data, index)) {
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
      const storage = getStorage(
        provider,
        prefix
      );
      if (!addIconSet(storage, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage.lastModifiedCached = storage.lastModifiedCached ? Math.min(storage.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}

function updateLastModified(storage, lastModified) {
  const lastValue = storage.lastModifiedCached;
  if (
    // Matches or newer
    lastValue && lastValue >= lastModified
  ) {
    return lastValue === lastModified;
  }
  storage.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage.provider || iconSet.prefix !== storage.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage, data) {
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
      if (index >= browserStorageLimit || !setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage.provider,
      data
    };
    return setStoredItem(
      func,
      browserCachePrefix + index.toString(),
      JSON.stringify(item)
    );
  }
  if (data.lastModified && !updateLastModified(storage, data.lastModified)) {
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
function loadedNewIcons(storage) {
  if (!storage.iconsLoaderFlag) {
    storage.iconsLoaderFlag = true;
    setTimeout(() => {
      storage.iconsLoaderFlag = false;
      updateCallbacks(storage);
    });
  }
}
function loadNewIcons(storage, icons) {
  if (!storage.iconsToLoad) {
    storage.iconsToLoad = icons;
  } else {
    storage.iconsToLoad = storage.iconsToLoad.concat(icons).sort();
  }
  if (!storage.iconsQueueFlag) {
    storage.iconsQueueFlag = true;
    setTimeout(() => {
      storage.iconsQueueFlag = false;
      const { provider, prefix } = storage;
      const icons2 = storage.iconsToLoad;
      delete storage.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(
                storage,
                data
              );
              if (!parsed.length) {
                return;
              }
              const pending = storage.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage);
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
          callback(
            sortedIcons.loaded,
            sortedIcons.missing,
            sortedIcons.pending,
            emptyCallback
          );
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
    const { provider, prefix } = icon;
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
    const { provider, prefix, name } = icon;
    const storage = getStorage(provider, prefix);
    const pendingQueue = storage.pendingIcons || (storage.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage) => {
    const { provider, prefix } = storage;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage, newIcons[provider][prefix]);
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
    inline: false,
};

/**
 * Default SVG attributes
 */
const svgDefaults = {
    'xmlns': 'http://www.w3.org/2000/svg',
    'xmlns:xlink': 'http://www.w3.org/1999/xlink',
    'aria-hidden': true,
    'role': 'img',
};
/**
 * Style modes
 */
const commonProps = {
    display: 'inline-block',
};
const monotoneProps = {
    'background-color': 'currentColor',
};
const coloredProps = {
    'background-color': 'transparent',
};
// Dynamically add common props to variables above
const propsToAdd = {
    image: 'var(--svg)',
    repeat: 'no-repeat',
    size: '100% 100%',
};
const propsToAddTo = {
    '-webkit-mask': monotoneProps,
    'mask': monotoneProps,
    'background': coloredProps,
};
for (const prefix in propsToAddTo) {
    const list = propsToAddTo[prefix];
    for (const prop in propsToAdd) {
        list[prefix + '-' + prop] = propsToAdd[prop];
    }
}
/**
 * Fix size: add 'px' to numbers
 */
function fixSize(value) {
    return value + (value.match(/^[-0-9.]+$/) ? 'px' : '');
}
/**
 * Generate icon from properties
 */
function render(
// Icon must be validated before calling this function
icon, 
// Properties
props) {
    const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
    // Check mode
    const mode = props.mode || 'svg';
    const componentProps = (mode === 'svg' ? { ...svgDefaults } : {});
    if (icon.body.indexOf('xlink:') === -1) {
        delete componentProps['xmlns:xlink'];
    }
    // Create style if missing
    let style = typeof props.style === 'string' ? props.style : '';
    // Get element properties
    for (let key in props) {
        const value = props[key];
        if (value === void 0) {
            continue;
        }
        switch (key) {
            // Properties to ignore
            case 'icon':
            case 'style':
            case 'onLoad':
            case 'mode':
                break;
            // Boolean attributes
            case 'inline':
            case 'hFlip':
            case 'vFlip':
                customisations[key] =
                    value === true || value === 'true' || value === 1;
                break;
            // Flip as string: 'horizontal,vertical'
            case 'flip':
                if (typeof value === 'string') {
                    flipFromString(customisations, value);
                }
                break;
            // Color: copy to style, add extra ';' in case style is missing it
            case 'color':
                style =
                    style +
                        (style.length > 0 && style.trim().slice(-1) !== ';'
                            ? ';'
                            : '') +
                        'color: ' +
                        value +
                        '; ';
                break;
            // Rotation as string
            case 'rotate':
                if (typeof value === 'string') {
                    customisations[key] = rotateFromString(value);
                }
                else if (typeof value === 'number') {
                    customisations[key] = value;
                }
                break;
            // Remove aria-hidden
            case 'ariaHidden':
            case 'aria-hidden':
                if (value !== true && value !== 'true') {
                    delete componentProps['aria-hidden'];
                }
                break;
            default:
                if (key.slice(0, 3) === 'on:') {
                    // Svelte event
                    break;
                }
                // Copy missing property if it does not exist in customisations
                if (defaultExtendedIconCustomisations[key] === void 0) {
                    componentProps[key] = value;
                }
        }
    }
    // Generate icon
    const item = iconToSVG(icon, customisations);
    const renderAttribs = item.attributes;
    // Inline display
    if (customisations.inline) {
        // Style overrides it
        style = 'vertical-align: -0.125em; ' + style;
    }
    if (mode === 'svg') {
        // Add icon stuff
        Object.assign(componentProps, renderAttribs);
        // Style
        if (style !== '') {
            componentProps.style = style;
        }
        // Counter for ids based on "id" property to render icons consistently on server and client
        let localCounter = 0;
        let id = props.id;
        if (typeof id === 'string') {
            // Convert '-' to '_' to avoid errors in animations
            id = id.replace(/-/g, '_');
        }
        // Generate HTML
        return {
            svg: true,
            attributes: componentProps,
            body: replaceIDs(item.body, id ? () => id + 'ID' + localCounter++ : 'iconifySvelte'),
        };
    }
    // Render <span> with style
    const { body, width, height } = icon;
    const useMask = mode === 'mask' ||
        (mode === 'bg' ? false : body.indexOf('currentColor') !== -1);
    // Generate SVG
    const html = iconToHTML(body, {
        ...renderAttribs,
        width: width + '',
        height: height + '',
    });
    // Generate style
    const url = svgToURL(html);
    const styles = {
        '--svg': url,
    };
    const size = (prop) => {
        const value = renderAttribs[prop];
        if (value) {
            styles[prop] = fixSize(value);
        }
    };
    size('width');
    size('height');
    Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
    let customStyle = '';
    for (const key in styles) {
        customStyle += key + ': ' + styles[key] + ';';
    }
    componentProps.style = customStyle + style;
    return {
        svg: false,
        attributes: componentProps,
    };
}
/**
 * Initialise stuff
 */
// Enable short names
allowSimpleNames(true);
// Set API module
setAPIModule('', fetchAPIModule);
/**
 * Browser stuff
 */
if (typeof document !== 'undefined' && typeof window !== 'undefined') {
    // Set cache and load existing cache
    initBrowserStorage();
    const _window = window;
    // Load icons from global "IconifyPreload"
    if (_window.IconifyPreload !== void 0) {
        const preload = _window.IconifyPreload;
        const err = 'Invalid IconifyPreload syntax.';
        if (typeof preload === 'object' && preload !== null) {
            (preload instanceof Array ? preload : [preload]).forEach((item) => {
                try {
                    if (
                    // Check if item is an object and not null/array
                    typeof item !== 'object' ||
                        item === null ||
                        item instanceof Array ||
                        // Check for 'icons' and 'prefix'
                        typeof item.icons !== 'object' ||
                        typeof item.prefix !== 'string' ||
                        // Add icon set
                        !addCollection(item)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            });
        }
    }
    // Set API from global "IconifyProviders"
    if (_window.IconifyProviders !== void 0) {
        const providers = _window.IconifyProviders;
        if (typeof providers === 'object' && providers !== null) {
            for (let key in providers) {
                const err = 'IconifyProviders[' + key + '] is invalid.';
                try {
                    const value = providers[key];
                    if (typeof value !== 'object' ||
                        !value ||
                        value.resources === void 0) {
                        continue;
                    }
                    if (!addAPIProvider(key, value)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            }
        }
    }
}
/**
 * Check if component needs to be updated
 */
function checkIconState(icon, state, mounted, callback, onload) {
    // Abort loading icon
    function abortLoading() {
        if (state.loading) {
            state.loading.abort();
            state.loading = null;
        }
    }
    // Icon is an object
    if (typeof icon === 'object' &&
        icon !== null &&
        typeof icon.body === 'string') {
        // Stop loading
        state.name = '';
        abortLoading();
        return { data: { ...defaultIconProps, ...icon } };
    }
    // Invalid icon?
    let iconName;
    if (typeof icon !== 'string' ||
        (iconName = stringToIcon(icon, false, true)) === null) {
        abortLoading();
        return null;
    }
    // Load icon
    const data = getIconData(iconName);
    if (!data) {
        // Icon data is not available
        // Do not load icon until component is mounted
        if (mounted && (!state.loading || state.loading.name !== icon)) {
            // New icon to load
            abortLoading();
            state.name = '';
            state.loading = {
                name: icon,
                abort: loadIcons([iconName], callback),
            };
        }
        return null;
    }
    // Icon data is available
    abortLoading();
    if (state.name !== icon) {
        state.name = icon;
        if (onload && !state.destroyed) {
            onload(icon);
        }
    }
    // Add classes
    const classes = ['iconify'];
    if (iconName.prefix !== '') {
        classes.push('iconify--' + iconName.prefix);
    }
    if (iconName.provider !== '') {
        classes.push('iconify--' + iconName.provider);
    }
    return { data, classes };
}
/**
 * Generate icon
 */
function generateIcon(icon, props) {
    return icon
        ? render({
            ...defaultIconProps,
            ...icon,
        }, props)
        : null;
}

/* generated by Svelte v3.59.1 */

function create_if_block$1(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1$1;
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

// (115:1) {:else}
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

// (111:1) {#if data.svg}
function create_if_block_1$1(ctx) {
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
	let if_block = /*data*/ ctx[0] && create_if_block$1(ctx);

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
					if_block = create_if_block$1(ctx);
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
			const iconData = checkIconState($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon(iconData.data, $$props) : null);

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

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i];
	return child_ctx;
}

// (93:2) {#if root_page}
function create_if_block_2(ctx) {
	let div;
	let t;

	return {
		c() {
			div = element("div");
			t = text(/*root_page*/ ctx[0]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, "data-key": true });
			var div_nodes = children(div);
			t = claim_text(div_nodes, /*root_page*/ ctx[0]);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "heading svelte-s4zn24");
			attr(div, "data-key", "root_page");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*root_page*/ 1) set_data(t, /*root_page*/ ctx[0]);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (115:4) {:catch error}
function create_catch_block(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text("promise was rejected");
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			var span_nodes = children(span);
			t = claim_text(span_nodes, "promise was rejected");
			span_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (99:4) {:then pages}
function create_then_block(ctx) {
	let ul;
	let each_value = /*pages*/ ctx[4];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	return {
		c() {
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			ul = claim_element(nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(ul, "class", "svelte-s4zn24");
		},
		m(target, anchor) {
			insert_hydration(target, ul, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}
		},
		p(ctx, dirty) {
			if (dirty & /*get_description, get_pages, get_title, parent_page*/ 6) {
				each_value = /*pages*/ ctx[4];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
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
			if (detaching) detach(ul);
			destroy_each(each_blocks, detaching);
		}
	};
}

// (104:12) {#if get_title(page) || get_description(page)}
function create_if_block(ctx) {
	let div1;
	let show_if = get_title(/*page*/ ctx[5]);
	let t;
	let div0;
	let raw_value = get_description(/*page*/ ctx[5]) + "";
	let if_block = show_if && create_if_block_1(ctx);

	return {
		c() {
			div1 = element("div");
			if (if_block) if_block.c();
			t = space();
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			if (if_block) if_block.l(div1_nodes);
			t = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "description");
			attr(div1, "class", "tooltip svelte-s4zn24");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			if (if_block) if_block.m(div1, null);
			append_hydration(div1, t);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (show_if) if_block.p(ctx, dirty);
		},
		d(detaching) {
			if (detaching) detach(div1);
			if (if_block) if_block.d();
		}
	};
}

// (106:16) {#if get_title(page)}
function create_if_block_1(ctx) {
	let div;
	let raw_value = get_title(/*page*/ ctx[5]) + "";

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
			attr(div, "class", "title svelte-s4zn24");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			div.innerHTML = raw_value;
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (101:8) {#each pages as page}
function create_each_block(ctx) {
	let li;
	let a;
	let t0_value = /*page*/ ctx[5].name + "";
	let t0;
	let a_href_value;
	let t1;
	let show_if = get_title(/*page*/ ctx[5]) || get_description(/*page*/ ctx[5]);
	let t2;
	let if_block = show_if && create_if_block(ctx);

	return {
		c() {
			li = element("li");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			if (if_block) if_block.l(li_nodes);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link underlined svelte-s4zn24");

			attr(a, "href", a_href_value = /*parent_page*/ ctx[1]
			? `${/*parent_page*/ ctx[1].url}/${/*page*/ ctx[5].url}`
			: `/${/*page*/ ctx[5].url}`);

			attr(li, "class", "svelte-s4zn24");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t0);
			append_hydration(li, t1);
			if (if_block) if_block.m(li, null);
			append_hydration(li, t2);
		},
		p(ctx, dirty) {
			if (dirty & /*parent_page*/ 2 && a_href_value !== (a_href_value = /*parent_page*/ ctx[1]
			? `${/*parent_page*/ ctx[1].url}/${/*page*/ ctx[5].url}`
			: `/${/*page*/ ctx[5].url}`)) {
				attr(a, "href", a_href_value);
			}

			if (show_if) if_block.p(ctx, dirty);
		},
		d(detaching) {
			if (detaching) detach(li);
			if (if_block) if_block.d();
		}
	};
}

// (97:24)        <Icon width="50" icon="line-md:loading-twotone-loop" />     {:then pages}
function create_pending_block(ctx) {
	let icon;
	let current;

	icon = new Component$1({
			props: {
				width: "50",
				icon: "line-md:loading-twotone-loop"
			}
		});

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
		p: noop,
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

// (96:2) {#key root_page}
function create_key_block(ctx) {
	let await_block_anchor;
	let current;

	let info = {
		ctx,
		current: null,
		token: null,
		hasCatch: true,
		pending: create_pending_block,
		then: create_then_block,
		catch: create_catch_block,
		value: 4,
		error: 8,
		blocks: [,,,]
	};

	handle_promise(/*get_pages*/ ctx[2](), info);

	return {
		c() {
			await_block_anchor = empty();
			info.block.c();
		},
		l(nodes) {
			await_block_anchor = empty();
			info.block.l(nodes);
		},
		m(target, anchor) {
			insert_hydration(target, await_block_anchor, anchor);
			info.block.m(target, info.anchor = anchor);
			info.mount = () => await_block_anchor.parentNode;
			info.anchor = await_block_anchor;
			current = true;
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			update_await_block_branch(info, ctx, dirty);
		},
		i(local) {
			if (current) return;
			transition_in(info.block);
			current = true;
		},
		o(local) {
			for (let i = 0; i < 3; i += 1) {
				const block = info.blocks[i];
				transition_out(block);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(await_block_anchor);
			info.block.d(detaching);
			info.token = null;
			info = null;
		}
	};
}

function create_fragment(ctx) {
	let div;
	let t;
	let previous_key = /*root_page*/ ctx[0];
	let current;
	let if_block = /*root_page*/ ctx[0] && create_if_block_2(ctx);
	let key_block = create_key_block(ctx);

	return {
		c() {
			div = element("div");
			if (if_block) if_block.c();
			t = space();
			key_block.c();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			if (if_block) if_block.l(div_nodes);
			t = claim_space(div_nodes);
			key_block.l(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "section-container");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			if (if_block) if_block.m(div, null);
			append_hydration(div, t);
			key_block.m(div, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if (/*root_page*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_2(ctx);
					if_block.c();
					if_block.m(div, t);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*root_page*/ 1 && safe_not_equal(previous_key, previous_key = /*root_page*/ ctx[0])) {
				group_outros();
				transition_out(key_block, 1, 1, noop);
				check_outros();
				key_block = create_key_block(ctx);
				key_block.c();
				transition_in(key_block, 1);
				key_block.m(div, null);
			} else {
				key_block.p(ctx, dirty);
			}
		},
		i(local) {
			if (current) return;
			transition_in(key_block);
			current = true;
		},
		o(local) {
			transition_out(key_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			if (if_block) if_block.d();
			key_block.d(detaching);
		}
	};
}

function get_title(page) {
	return page.sections[1]["content"]["en"]["heading"] || null;
}

function get_description(page) {
	return page.sections[1]["content"]["en"]["content"]
	? page.sections[1]["content"]["en"]["content"].html
	: null;
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { root_page } = $$props;
	let parent_page = {};

	async function get_pages() {
		const data = await axios.get("/primo.json").then(res => {
			console.log(res);
			return res.data;
		});

		console.log({ data });
		$$invalidate(1, parent_page = data.pages.find(page => page.name === root_page));

		// console.log(data);
		if (root_page) {
			const child_pages = data.pages.filter(page => page.parent === parent_page.id).map(page => ({
				...page,
				sections: data.sections.filter(section => section.page === page.id).sort((a, b) => a.index - b.index)
			}));

			// console.log({ child_pages });
			return child_pages;
		} else {
			return data.pages;
		}
	}

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(3, props = $$props.props);
		if ('root_page' in $$props) $$invalidate(0, root_page = $$props.root_page);
	};

	return [root_page, parent_page, get_pages, props];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 3, root_page: 0 });
	}
}

export { Component as default };
