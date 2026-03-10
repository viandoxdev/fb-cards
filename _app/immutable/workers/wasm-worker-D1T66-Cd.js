(async ()=>{
    var N = "" + new URL("assets/fb_web_bg-CW_WeNIM.wasm", import.meta.url).href, J = async (e = {}, _)=>{
        let t;
        if (_.startsWith("data:")) {
            const s = _.replace(/^data:.*?base64,/, "");
            let o;
            if (typeof Buffer == "function" && typeof Buffer.from == "function") o = Buffer.from(s, "base64");
            else if (typeof atob == "function") {
                const a = atob(s);
                o = new Uint8Array(a.length);
                for(let c = 0; c < a.length; c++)o[c] = a.charCodeAt(c);
            } else throw new Error("Cannot decode base64-encoded data URL");
            t = await WebAssembly.instantiate(o, e);
        } else {
            const s = await fetch(_), o = s.headers.get("Content-Type") || "";
            if ("instantiateStreaming" in WebAssembly && o.startsWith("application/wasm")) t = await WebAssembly.instantiateStreaming(s, e);
            else {
                const a = await s.arrayBuffer();
                t = await WebAssembly.instantiate(a, e);
            }
        }
        return t.instance.exports;
    };
    class b {
        static __unwrap(_) {
            return _ instanceof b ? _.__destroy_into_raw() : 0;
        }
        __destroy_into_raw() {
            const _ = this.__wbg_ptr;
            return this.__wbg_ptr = 0, S.unregister(this), _;
        }
        free() {
            const _ = this.__destroy_into_raw();
            r.__wbg_card_free(_, 0);
        }
        constructor(_, t, s, o, a, c){
            var g = T(_) ? 0 : w(_, r.__wbindgen_malloc, r.__wbindgen_realloc), f = i;
            const B = w(t, r.__wbindgen_malloc, r.__wbindgen_realloc), D = i, U = w(s, r.__wbindgen_malloc, r.__wbindgen_realloc), I = i, L = w(o, r.__wbindgen_malloc, r.__wbindgen_realloc), O = i, k = w(a, r.__wbindgen_malloc, r.__wbindgen_realloc), V = i, j = W(c, r.__wbindgen_malloc), P = i, G = r.card_new(g, f, B, D, U, I, L, O, k, V, j, P);
            return this.__wbg_ptr = G >>> 0, S.register(this, this.__wbg_ptr, this), this;
        }
    }
    Symbol.dispose && (b.prototype[Symbol.dispose] = b.prototype.free);
    class p {
        static __wrap(_) {
            _ = _ >>> 0;
            const t = Object.create(p.prototype);
            return t.__wbg_ptr = _, R.register(t, t.__wbg_ptr, t), t;
        }
        __destroy_into_raw() {
            const _ = this.__wbg_ptr;
            return this.__wbg_ptr = 0, R.unregister(this), _;
        }
        free() {
            const _ = this.__destroy_into_raw();
            r.__wbg_cardpage_free(_, 0);
        }
        svg() {
            let _, t;
            try {
                const s = r.cardpage_svg(this.__wbg_ptr);
                return _ = s[0], t = s[1], h(s[0], s[1]);
            } finally{
                r.__wbindgen_free(_, t, 1);
            }
        }
    }
    Symbol.dispose && (p.prototype[Symbol.dispose] = p.prototype.free);
    class A {
        __destroy_into_raw() {
            const _ = this.__wbg_ptr;
            return this.__wbg_ptr = 0, E.unregister(this), _;
        }
        free() {
            const _ = this.__destroy_into_raw();
            r.__wbg_core_free(_, 0);
        }
        compile() {
            const _ = r.core_compile(this.__wbg_ptr);
            if (_[3]) throw q(_[2]);
            var t = g_(_[0], _[1]).slice();
            return r.__wbindgen_free(_[0], _[1] * 4, 4), t;
        }
        constructor(_){
            const t = f_(_, r.__wbindgen_malloc), s = i, o = r.core_new(t, s);
            if (o[2]) throw q(o[1]);
            return this.__wbg_ptr = o[0] >>> 0, E.register(this, this.__wbg_ptr, this), this;
        }
        prepare_source(_, t) {
            const s = W(_, r.__wbindgen_malloc), o = i;
            i_(t, z);
            var a = t.__destroy_into_raw();
            const c = r.core_prepare_source(this.__wbg_ptr, s, o, a);
            if (c[1]) throw q(c[0]);
        }
    }
    Symbol.dispose && (A.prototype[Symbol.dispose] = A.prototype.free);
    class z {
        __destroy_into_raw() {
            const _ = this.__wbg_ptr;
            return this.__wbg_ptr = 0, F.unregister(this), _;
        }
        free() {
            const _ = this.__destroy_into_raw();
            r.__wbg_sourceconfig_free(_, 0);
        }
        get page_width() {
            return r.__wbg_get_sourceconfig_page_width(this.__wbg_ptr) >>> 0;
        }
        get sans_math() {
            return r.__wbg_get_sourceconfig_sans_math(this.__wbg_ptr) !== 0;
        }
        get text_color() {
            return r.__wbg_get_sourceconfig_text_color(this.__wbg_ptr) >>> 0;
        }
        get text_size() {
            return r.__wbg_get_sourceconfig_text_size(this.__wbg_ptr) >>> 0;
        }
        set page_width(_) {
            r.__wbg_set_sourceconfig_page_width(this.__wbg_ptr, _);
        }
        set sans_math(_) {
            r.__wbg_set_sourceconfig_sans_math(this.__wbg_ptr, _);
        }
        set text_color(_) {
            r.__wbg_set_sourceconfig_text_color(this.__wbg_ptr, _);
        }
        set text_size(_) {
            r.__wbg_set_sourceconfig_text_size(this.__wbg_ptr, _);
        }
        constructor(_, t, s, o){
            const a = r.sourceconfig_new(_, t, s, o);
            return this.__wbg_ptr = a >>> 0, F.register(this, this.__wbg_ptr, this), this;
        }
    }
    Symbol.dispose && (z.prototype[Symbol.dispose] = z.prototype.free);
    function $(e, _) {
        return Error(h(e, _));
    }
    function X(e, _) {
        const t = _, s = typeof t == "string" ? t : void 0;
        var o = T(s) ? 0 : w(s, r.__wbindgen_malloc, r.__wbindgen_realloc), a = i;
        u().setInt32(e + 4, a, !0), u().setInt32(e + 0, o, !0);
    }
    function Y(e, _) {
        throw new Error(h(e, _));
    }
    function H(e) {
        return b.__unwrap(e);
    }
    function K(e) {
        return p.__wrap(e);
    }
    function Q(e) {
        console.debug(e);
    }
    function Z(e) {
        console.error(e);
    }
    function __(e, _) {
        let t, s;
        try {
            t = e, s = _, console.error(h(e, _));
        } finally{
            r.__wbindgen_free(t, s, 1);
        }
    }
    function e_(e) {
        console.info(e);
    }
    function t_(e) {
        console.log(e);
    }
    function r_() {
        return new Error;
    }
    function n_(e, _) {
        const t = _.stack, s = w(t, r.__wbindgen_malloc, r.__wbindgen_realloc), o = i;
        u().setInt32(e + 4, o, !0), u().setInt32(e + 0, s, !0);
    }
    function s_(e) {
        console.warn(e);
    }
    function o_(e, _) {
        return h(e, _);
    }
    function c_() {
        const e = r.__wbindgen_externrefs, _ = e.grow(4);
        e.set(0, void 0), e.set(_ + 0, void 0), e.set(_ + 1, null), e.set(_ + 2, !0), e.set(_ + 3, !1);
    }
    const S = typeof FinalizationRegistry > "u" ? {
        register: ()=>{},
        unregister: ()=>{}
    } : new FinalizationRegistry((e)=>r.__wbg_card_free(e >>> 0, 1)), R = typeof FinalizationRegistry > "u" ? {
        register: ()=>{},
        unregister: ()=>{}
    } : new FinalizationRegistry((e)=>r.__wbg_cardpage_free(e >>> 0, 1)), E = typeof FinalizationRegistry > "u" ? {
        register: ()=>{},
        unregister: ()=>{}
    } : new FinalizationRegistry((e)=>r.__wbg_core_free(e >>> 0, 1)), F = typeof FinalizationRegistry > "u" ? {
        register: ()=>{},
        unregister: ()=>{}
    } : new FinalizationRegistry((e)=>r.__wbg_sourceconfig_free(e >>> 0, 1));
    function a_(e) {
        const _ = r.__externref_table_alloc();
        return r.__wbindgen_externrefs.set(_, e), _;
    }
    function i_(e, _) {
        if (!(e instanceof _)) throw new Error(`expected instance of ${_.name}`);
    }
    function g_(e, _) {
        e = e >>> 0;
        const t = u(), s = [];
        for(let o = e; o < e + 4 * _; o += 4)s.push(r.__wbindgen_externrefs.get(t.getUint32(o, !0)));
        return r.__externref_drop_slice(e, _), s;
    }
    let d = null;
    function u() {
        return (d === null || d.buffer.detached === !0 || d.buffer.detached === void 0 && d.buffer !== r.memory.buffer) && (d = new DataView(r.memory.buffer)), d;
    }
    function h(e, _) {
        return e = e >>> 0, d_(e, _);
    }
    let y = null;
    function l() {
        return (y === null || y.byteLength === 0) && (y = new Uint8Array(r.memory.buffer)), y;
    }
    function T(e) {
        return e == null;
    }
    function f_(e, _) {
        const t = _(e.length * 1, 1) >>> 0;
        return l().set(e, t / 1), i = e.length, t;
    }
    function W(e, _) {
        const t = _(e.length * 4, 4) >>> 0;
        for(let s = 0; s < e.length; s++){
            const o = a_(e[s]);
            u().setUint32(t + 4 * s, o, !0);
        }
        return i = e.length, t;
    }
    function w(e, _, t) {
        if (t === void 0) {
            const g = m.encode(e), f = _(g.length, 1) >>> 0;
            return l().subarray(f, f + g.length).set(g), i = g.length, f;
        }
        let s = e.length, o = _(s, 1) >>> 0;
        const a = l();
        let c = 0;
        for(; c < s; c++){
            const g = e.charCodeAt(c);
            if (g > 127) break;
            a[o + c] = g;
        }
        if (c !== s) {
            c !== 0 && (e = e.slice(c)), o = t(o, s, s = c + e.length * 3, 1) >>> 0;
            const g = l().subarray(o + c, o + s), f = m.encodeInto(e, g);
            c += f.written, o = t(o, s, c, 1) >>> 0;
        }
        return i = c, o;
    }
    function q(e) {
        const _ = r.__wbindgen_externrefs.get(e);
        return r.__externref_table_dealloc(e), _;
    }
    let x = new TextDecoder("utf-8", {
        ignoreBOM: !0,
        fatal: !0
    });
    x.decode();
    const w_ = 2146435072;
    let v = 0;
    function d_(e, _) {
        return v += _, v >= w_ && (x = new TextDecoder("utf-8", {
            ignoreBOM: !0,
            fatal: !0
        }), x.decode(), v = _), x.decode(l().subarray(e, e + _));
    }
    const m = new TextEncoder;
    "encodeInto" in m || (m.encodeInto = function(e, _) {
        const t = m.encode(e);
        return _.set(t), {
            read: e.length,
            written: t.length
        };
    });
    let i = 0, r;
    function b_(e) {
        r = e;
    }
    URL = globalThis.URL;
    const n = await J({
        "./fb_web_bg.js": {
            __wbg_card_unwrap: H,
            __wbg_log_524eedafa26daa59: t_,
            __wbg_info_7d4e223bb1a7e671: e_,
            __wbg_warn_69424c2d92a2fa73: s_,
            __wbg_debug_4b9b1a2d5972be57: Q,
            __wbg_error_8d9a8e04cd1d3588: Z,
            __wbg_new_227d7c05414eb861: r_,
            __wbg_stack_3b0d974bbf31e44f: n_,
            __wbg_error_a6fa202b58aa1cd3: __,
            __wbg_cardpage_new: K,
            __wbg___wbindgen_string_get_395e606bd0ee4427: X,
            __wbg___wbindgen_throw_6ddd609b62940d55: Y,
            __wbg_Error_83742b46f01ce22d: $,
            __wbindgen_init_externref_table: c_,
            __wbindgen_cast_0000000000000001: o_
        }
    }, N), u_ = n.memory, l_ = n.__wbg_core_free, m_ = n.core_compile, p_ = n.core_new, h_ = n.core_prepare_source, y_ = n.start, x_ = n.__wbg_card_free, z_ = n.card_new, q_ = n.rust_zstd_wasm_shim_calloc, v_ = n.rust_zstd_wasm_shim_free, A_ = n.rust_zstd_wasm_shim_malloc, C_ = n.rust_zstd_wasm_shim_memcmp, S_ = n.rust_zstd_wasm_shim_memcpy, R_ = n.rust_zstd_wasm_shim_memmove, E_ = n.rust_zstd_wasm_shim_memset, F_ = n.rust_zstd_wasm_shim_qsort, T_ = n.__wbg_cardpage_free, W_ = n.cardpage_svg, M_ = n.__wbg_get_sourceconfig_page_width, B_ = n.__wbg_get_sourceconfig_sans_math, D_ = n.__wbg_get_sourceconfig_text_color, U_ = n.__wbg_get_sourceconfig_text_size, I_ = n.__wbg_set_sourceconfig_page_width, L_ = n.__wbg_set_sourceconfig_sans_math, O_ = n.__wbg_set_sourceconfig_text_color, k_ = n.__wbg_set_sourceconfig_text_size, V_ = n.__wbg_sourceconfig_free, j_ = n.sourceconfig_new, P_ = n.qcms_enable_iccv4, G_ = n.qcms_profile_precache_output_transform, N_ = n.qcms_transform_data_bgra_out_lut, J_ = n.qcms_transform_data_bgra_out_lut_precache, $_ = n.qcms_transform_data_rgb_out_lut, X_ = n.qcms_transform_data_rgb_out_lut_precache, Y_ = n.qcms_transform_data_rgba_out_lut, H_ = n.qcms_transform_data_rgba_out_lut_precache, K_ = n.qcms_transform_release, Q_ = n.qcms_profile_is_bogus, Z_ = n.qcms_white_point_sRGB, _e = n.lut_inverse_interp16, ee = n.lut_interp_linear16, te = n.__wbindgen_malloc, re = n.__wbindgen_realloc, ne = n.__wbindgen_free, se = n.__wbindgen_externrefs, oe = n.__externref_table_alloc, ce = n.__externref_table_dealloc, ae = n.__externref_drop_slice, M = n.__wbindgen_start;
    var ie = Object.freeze({
        __proto__: null,
        __externref_drop_slice: ae,
        __externref_table_alloc: oe,
        __externref_table_dealloc: ce,
        __wbg_card_free: x_,
        __wbg_cardpage_free: T_,
        __wbg_core_free: l_,
        __wbg_get_sourceconfig_page_width: M_,
        __wbg_get_sourceconfig_sans_math: B_,
        __wbg_get_sourceconfig_text_color: D_,
        __wbg_get_sourceconfig_text_size: U_,
        __wbg_set_sourceconfig_page_width: I_,
        __wbg_set_sourceconfig_sans_math: L_,
        __wbg_set_sourceconfig_text_color: O_,
        __wbg_set_sourceconfig_text_size: k_,
        __wbg_sourceconfig_free: V_,
        __wbindgen_externrefs: se,
        __wbindgen_free: ne,
        __wbindgen_malloc: te,
        __wbindgen_realloc: re,
        __wbindgen_start: M,
        card_new: z_,
        cardpage_svg: W_,
        core_compile: m_,
        core_new: p_,
        core_prepare_source: h_,
        lut_interp_linear16: ee,
        lut_inverse_interp16: _e,
        memory: u_,
        qcms_enable_iccv4: P_,
        qcms_profile_is_bogus: Q_,
        qcms_profile_precache_output_transform: G_,
        qcms_transform_data_bgra_out_lut: N_,
        qcms_transform_data_bgra_out_lut_precache: J_,
        qcms_transform_data_rgb_out_lut: $_,
        qcms_transform_data_rgb_out_lut_precache: X_,
        qcms_transform_data_rgba_out_lut: Y_,
        qcms_transform_data_rgba_out_lut_precache: H_,
        qcms_transform_release: K_,
        qcms_white_point_sRGB: Z_,
        rust_zstd_wasm_shim_calloc: q_,
        rust_zstd_wasm_shim_free: v_,
        rust_zstd_wasm_shim_malloc: A_,
        rust_zstd_wasm_shim_memcmp: C_,
        rust_zstd_wasm_shim_memcpy: S_,
        rust_zstd_wasm_shim_memmove: R_,
        rust_zstd_wasm_shim_memset: E_,
        rust_zstd_wasm_shim_qsort: F_,
        sourceconfig_new: j_,
        start: y_
    });
    b_(ie);
    M();
    let C;
    const ge = (async ()=>{
        const _ = await (await fetch("/data-bundle.zip")).arrayBuffer();
        C = new A(new Uint8Array(_));
    })();
    self.onmessage = async (e)=>{
        await ge;
        const _ = e.data;
        if (_.type === "COMPILE_CARD") {
            const t = _.payload.card;
            C.prepare_source([
                new b(t.header, t.id, t.name, t.question, t.answer, t.locations)
            ], new z(_.payload.config.pageWidth, _.payload.config.fontSize, _.payload.config.textColor, _.payload.config.useSansFont));
            const s = C.compile();
            let o = [
                s[1].svg(),
                s[2].svg()
            ];
            self.postMessage({
                type: "COMPILED_CARD",
                payload: o
            });
        }
    };
})();
