// Super Footer - Updated August 7, 2023
function noop() { }
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
function element(name) {
    return document.createElement(name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
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
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}

let current_component;
function set_current_component(component) {
    current_component = component;
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
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
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
			section = claim_element(nodes, "SECTION", { class: true });
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
			t18 = claim_space(nodes);

			link = claim_element(nodes, "LINK", {
				rel: true,
				href: true,
				integrity: true,
				crossorigin: true,
				referrerpolicy: true
			});

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
		},
		m(target, anchor) {
			insert_hydration(target, section, anchor);
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
			insert_hydration(target, t18, anchor);
			insert_hydration(target, link, anchor);
		},
		p(ctx, [dirty]) {
			if (dirty & /*signup_form*/ 1 && t0_value !== (t0_value = /*signup_form*/ ctx[0].heading + "")) set_data(t0, t0_value);
			if (dirty & /*signup_form*/ 1 && raw_value !== (raw_value = /*signup_form*/ ctx[0].subheading.html + "")) h3.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(section);
			if (detaching) detach(t18);
			if (detaching) detach(link);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { signup_form } = $$props;

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(1, props = $$props.props);
		if ('signup_form' in $$props) $$invalidate(0, signup_form = $$props.signup_form);
	};

	return [signup_form, props];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 1, signup_form: 0 });
	}
}

export default Component;
