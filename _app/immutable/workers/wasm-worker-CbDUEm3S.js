(async ()=>{
    var X = "" + new URL("assets/fb_web_bg-B4IZ-NR6.wasm", import.meta.url).href, Z = async (t = {}, _)=>{
        let e;
        if (_.startsWith("data:")) {
            const s = _.replace(/^data:.*?base64,/, "");
            let o;
            if (typeof Buffer == "function" && typeof Buffer.from == "function") o = Buffer.from(s, "base64");
            else if (typeof atob == "function") {
                const i = atob(s);
                o = new Uint8Array(i.length);
                for(let c = 0; c < i.length; c++)o[c] = i.charCodeAt(c);
            } else throw new Error("Cannot decode base64-encoded data URL");
            e = await WebAssembly.instantiate(o, t);
        } else {
            const s = await fetch(_), o = s.headers.get("Content-Type") || "";
            if ("instantiateStreaming" in WebAssembly && o.startsWith("application/wasm")) e = await WebAssembly.instantiateStreaming(s, t);
            else {
                const i = await s.arrayBuffer();
                e = await WebAssembly.instantiate(i, t);
            }
        }
        return e.instance.exports;
    };
    class l {
        static __unwrap(_) {
            return _ instanceof l ? _.__destroy_into_raw() : 0;
        }
        __destroy_into_raw() {
            const _ = this.__wbg_ptr;
            return this.__wbg_ptr = 0, F.unregister(this), _;
        }
        free() {
            const _ = this.__destroy_into_raw();
            r.__wbg_card_free(_, 0);
        }
        constructor(_, e, s, o, i, c){
            var g = W(_) ? 0 : f(_, r.__wbindgen_export, r.__wbindgen_export2), u = d;
            const O = f(e, r.__wbindgen_export, r.__wbindgen_export2), j = d, L = f(s, r.__wbindgen_export, r.__wbindgen_export2), P = d, V = f(o, r.__wbindgen_export, r.__wbindgen_export2), N = d, G = f(i, r.__wbindgen_export, r.__wbindgen_export2), J = d, Y = B(c, r.__wbindgen_export), $ = d, H = r.card_new(g, u, O, j, L, P, V, N, G, J, Y, $);
            return this.__wbg_ptr = H >>> 0, F.register(this, this.__wbg_ptr, this), this;
        }
    }
    Symbol.dispose && (l.prototype[Symbol.dispose] = l.prototype.free);
    class z {
        static __wrap(_) {
            _ = _ >>> 0;
            const e = Object.create(z.prototype);
            return e.__wbg_ptr = _, k.register(e, e.__wbg_ptr, e), e;
        }
        __destroy_into_raw() {
            const _ = this.__wbg_ptr;
            return this.__wbg_ptr = 0, k.unregister(this), _;
        }
        free() {
            const _ = this.__destroy_into_raw();
            r.__wbg_cardpage_free(_, 0);
        }
        svg() {
            let _, e;
            try {
                const i = r.__wbindgen_add_to_stack_pointer(-16);
                r.cardpage_svg(i, this.__wbg_ptr);
                var s = a().getInt32(i + 0, !0), o = a().getInt32(i + 4, !0);
                return _ = s, e = o, q(s, o);
            } finally{
                r.__wbindgen_add_to_stack_pointer(16), r.__wbindgen_export3(_, e, 1);
            }
        }
    }
    Symbol.dispose && (z.prototype[Symbol.dispose] = z.prototype.free);
    class E {
        __destroy_into_raw() {
            const _ = this.__wbg_ptr;
            return this.__wbg_ptr = 0, T.unregister(this), _;
        }
        free() {
            const _ = this.__destroy_into_raw();
            r.__wbg_core_free(_, 0);
        }
        compile() {
            try {
                const c = r.__wbindgen_add_to_stack_pointer(-16);
                r.core_compile(c, this.__wbg_ptr);
                var _ = a().getInt32(c + 0, !0), e = a().getInt32(c + 4, !0), s = a().getInt32(c + 8, !0), o = a().getInt32(c + 12, !0);
                if (o) throw y(s);
                var i = f_(_, e).slice();
                return r.__wbindgen_export3(_, e * 4, 4), i;
            } finally{
                r.__wbindgen_add_to_stack_pointer(16);
            }
        }
        constructor(_){
            try {
                const i = r.__wbindgen_add_to_stack_pointer(-16), c = p_(_, r.__wbindgen_export), g = d;
                r.core_new(i, c, g);
                var e = a().getInt32(i + 0, !0), s = a().getInt32(i + 4, !0), o = a().getInt32(i + 8, !0);
                if (o) throw y(s);
                return this.__wbg_ptr = e >>> 0, T.register(this, this.__wbg_ptr, this), this;
            } finally{
                r.__wbindgen_add_to_stack_pointer(16);
            }
        }
        prepare_source(_, e) {
            try {
                const c = r.__wbindgen_add_to_stack_pointer(-16), g = B(_, r.__wbindgen_export), u = d;
                w_(e, R);
                var s = e.__destroy_into_raw();
                r.core_prepare_source(c, this.__wbg_ptr, g, u, s);
                var o = a().getInt32(c + 0, !0), i = a().getInt32(c + 4, !0);
                if (i) throw y(o);
            } finally{
                r.__wbindgen_add_to_stack_pointer(16);
            }
        }
    }
    Symbol.dispose && (E.prototype[Symbol.dispose] = E.prototype.free);
    class R {
        __destroy_into_raw() {
            const _ = this.__wbg_ptr;
            return this.__wbg_ptr = 0, U.unregister(this), _;
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
        constructor(_, e, s, o){
            const i = r.sourceconfig_new(_, e, s, o);
            return this.__wbg_ptr = i >>> 0, U.register(this, this.__wbg_ptr, this), this;
        }
    }
    Symbol.dispose && (R.prototype[Symbol.dispose] = R.prototype.free);
    function K(t, _) {
        const e = Error(q(t, _));
        return v(e);
    }
    function Q(t, _) {
        const e = b(_), s = typeof e == "string" ? e : void 0;
        var o = W(s) ? 0 : f(s, r.__wbindgen_export, r.__wbindgen_export2), i = d;
        a().setInt32(t + 4, i, !0), a().setInt32(t + 0, o, !0);
    }
    function __(t, _) {
        throw new Error(q(t, _));
    }
    function t_(t) {
        return l.__unwrap(b(t));
    }
    function e_(t) {
        const _ = z.__wrap(t);
        return v(_);
    }
    function r_(t) {
        console.debug(b(t));
    }
    function n_(t) {
        console.error(b(t));
    }
    function s_(t, _) {
        let e, s;
        try {
            e = t, s = _, console.error(q(t, _));
        } finally{
            r.__wbindgen_export3(e, s, 1);
        }
    }
    function o_(t) {
        console.info(b(t));
    }
    function c_(t) {
        console.log(b(t));
    }
    function i_() {
        const t = new Error;
        return v(t);
    }
    function a_(t, _) {
        const e = b(_).stack, s = f(e, r.__wbindgen_export, r.__wbindgen_export2), o = d;
        a().setInt32(t + 4, o, !0), a().setInt32(t + 0, s, !0);
    }
    function g_(t) {
        console.warn(b(t));
    }
    function d_(t, _) {
        const e = q(t, _);
        return v(e);
    }
    function u_(t) {
        y(t);
    }
    const F = typeof FinalizationRegistry > "u" ? {
        register: ()=>{},
        unregister: ()=>{}
    } : new FinalizationRegistry((t)=>r.__wbg_card_free(t >>> 0, 1)), k = typeof FinalizationRegistry > "u" ? {
        register: ()=>{},
        unregister: ()=>{}
    } : new FinalizationRegistry((t)=>r.__wbg_cardpage_free(t >>> 0, 1)), T = typeof FinalizationRegistry > "u" ? {
        register: ()=>{},
        unregister: ()=>{}
    } : new FinalizationRegistry((t)=>r.__wbg_core_free(t >>> 0, 1)), U = typeof FinalizationRegistry > "u" ? {
        register: ()=>{},
        unregister: ()=>{}
    } : new FinalizationRegistry((t)=>r.__wbg_sourceconfig_free(t >>> 0, 1));
    function v(t) {
        h === w.length && w.push(w.length + 1);
        const _ = h;
        return h = w[_], w[_] = t, _;
    }
    function w_(t, _) {
        if (!(t instanceof _)) throw new Error(`expected instance of ${_.name}`);
    }
    function b_(t) {
        t < 1028 || (w[t] = h, h = t);
    }
    function f_(t, _) {
        t = t >>> 0;
        const e = a(), s = [];
        for(let o = t; o < t + 4 * _; o += 4)s.push(y(e.getUint32(o, !0)));
        return s;
    }
    let p = null;
    function a() {
        return (p === null || p.buffer.detached === !0 || p.buffer.detached === void 0 && p.buffer !== r.memory.buffer) && (p = new DataView(r.memory.buffer)), p;
    }
    function q(t, _) {
        return t = t >>> 0, m_(t, _);
    }
    let I = null;
    function m() {
        return (I === null || I.byteLength === 0) && (I = new Uint8Array(r.memory.buffer)), I;
    }
    function b(t) {
        return w[t];
    }
    let w = new Array(1024).fill(void 0);
    w.push(void 0, null, !0, !1);
    let h = w.length;
    function W(t) {
        return t == null;
    }
    function p_(t, _) {
        const e = _(t.length * 1, 1) >>> 0;
        return m().set(t, e / 1), d = t.length, e;
    }
    function B(t, _) {
        const e = _(t.length * 4, 4) >>> 0, s = a();
        for(let o = 0; o < t.length; o++)s.setUint32(e + 4 * o, v(t[o]), !0);
        return d = t.length, e;
    }
    function f(t, _, e) {
        if (e === void 0) {
            const g = x.encode(t), u = _(g.length, 1) >>> 0;
            return m().subarray(u, u + g.length).set(g), d = g.length, u;
        }
        let s = t.length, o = _(s, 1) >>> 0;
        const i = m();
        let c = 0;
        for(; c < s; c++){
            const g = t.charCodeAt(c);
            if (g > 127) break;
            i[o + c] = g;
        }
        if (c !== s) {
            c !== 0 && (t = t.slice(c)), o = e(o, s, s = c + t.length * 3, 1) >>> 0;
            const g = m().subarray(o + c, o + s), u = x.encodeInto(t, g);
            c += u.written, o = e(o, s, c, 1) >>> 0;
        }
        return d = c, o;
    }
    function y(t) {
        const _ = b(t);
        return b_(t), _;
    }
    let A = new TextDecoder("utf-8", {
        ignoreBOM: !0,
        fatal: !0
    });
    A.decode();
    const l_ = 2146435072;
    let C = 0;
    function m_(t, _) {
        return C += _, C >= l_ && (A = new TextDecoder("utf-8", {
            ignoreBOM: !0,
            fatal: !0
        }), A.decode(), C = _), A.decode(m().subarray(t, t + _));
    }
    const x = new TextEncoder;
    "encodeInto" in x || (x.encodeInto = function(t, _) {
        const e = x.encode(t);
        return _.set(e), {
            read: t.length,
            written: e.length
        };
    });
    let d = 0, r;
    function h_(t) {
        r = t;
    }
    URL = globalThis.URL;
    const n = await Z({
        "./fb_web_bg.js": {
            __wbg_Error_83742b46f01ce22d: K,
            __wbg_cardpage_new: e_,
            __wbg_card_unwrap: t_,
            __wbindgen_object_drop_ref: u_,
            __wbg_new_227d7c05414eb861: i_,
            __wbg_stack_3b0d974bbf31e44f: a_,
            __wbg_error_a6fa202b58aa1cd3: s_,
            __wbg___wbindgen_string_get_395e606bd0ee4427: Q,
            __wbg___wbindgen_throw_6ddd609b62940d55: __,
            __wbg_log_524eedafa26daa59: c_,
            __wbg_info_7d4e223bb1a7e671: o_,
            __wbg_warn_69424c2d92a2fa73: g_,
            __wbg_debug_4b9b1a2d5972be57: r_,
            __wbg_error_8d9a8e04cd1d3588: n_,
            __wbindgen_cast_0000000000000001: d_
        }
    }, X), y_ = n.memory, x_ = n.__wbg_core_free, z_ = n.core_compile, v_ = n.core_new, q_ = n.core_prepare_source, I_ = n.start, A_ = n.__wbg_cardpage_free, R_ = n.cardpage_svg, C_ = n.__wbg_get_sourceconfig_page_width, S_ = n.__wbg_get_sourceconfig_sans_math, E_ = n.__wbg_get_sourceconfig_text_color, F_ = n.__wbg_get_sourceconfig_text_size, k_ = n.__wbg_set_sourceconfig_page_width, T_ = n.__wbg_set_sourceconfig_sans_math, U_ = n.__wbg_set_sourceconfig_text_color, W_ = n.__wbg_set_sourceconfig_text_size, B_ = n.__wbg_sourceconfig_free, D_ = n.sourceconfig_new, M_ = n.__wbg_card_free, O_ = n.card_new, j_ = n.qcms_transform_data_rgb_out_lut, L_ = n.qcms_transform_data_rgba_out_lut, P_ = n.qcms_transform_data_bgra_out_lut, V_ = n.qcms_transform_data_rgb_out_lut_precache, N_ = n.qcms_transform_data_rgba_out_lut_precache, G_ = n.qcms_transform_data_bgra_out_lut_precache, J_ = n.qcms_profile_precache_output_transform, Y_ = n.qcms_transform_release, $_ = n.qcms_profile_is_bogus, H_ = n.qcms_white_point_sRGB, X_ = n.lut_inverse_interp16, Z_ = n.lut_interp_linear16, K_ = n.rust_zstd_wasm_shim_calloc, Q_ = n.rust_zstd_wasm_shim_free, _t = n.rust_zstd_wasm_shim_malloc, tt = n.rust_zstd_wasm_shim_memcmp, et = n.rust_zstd_wasm_shim_memcpy, rt = n.rust_zstd_wasm_shim_memmove, nt = n.rust_zstd_wasm_shim_memset, st = n.rust_zstd_wasm_shim_qsort, ot = n.qcms_enable_iccv4, ct = n.__wbindgen_export, it = n.__wbindgen_export2, at = n.__wbindgen_export3, gt = n.__wbindgen_add_to_stack_pointer, D = n.__wbindgen_start;
    var dt = Object.freeze({
        __proto__: null,
        __wbg_card_free: M_,
        __wbg_cardpage_free: A_,
        __wbg_core_free: x_,
        __wbg_get_sourceconfig_page_width: C_,
        __wbg_get_sourceconfig_sans_math: S_,
        __wbg_get_sourceconfig_text_color: E_,
        __wbg_get_sourceconfig_text_size: F_,
        __wbg_set_sourceconfig_page_width: k_,
        __wbg_set_sourceconfig_sans_math: T_,
        __wbg_set_sourceconfig_text_color: U_,
        __wbg_set_sourceconfig_text_size: W_,
        __wbg_sourceconfig_free: B_,
        __wbindgen_add_to_stack_pointer: gt,
        __wbindgen_export: ct,
        __wbindgen_export2: it,
        __wbindgen_export3: at,
        __wbindgen_start: D,
        card_new: O_,
        cardpage_svg: R_,
        core_compile: z_,
        core_new: v_,
        core_prepare_source: q_,
        lut_interp_linear16: Z_,
        lut_inverse_interp16: X_,
        memory: y_,
        qcms_enable_iccv4: ot,
        qcms_profile_is_bogus: $_,
        qcms_profile_precache_output_transform: J_,
        qcms_transform_data_bgra_out_lut: P_,
        qcms_transform_data_bgra_out_lut_precache: G_,
        qcms_transform_data_rgb_out_lut: j_,
        qcms_transform_data_rgb_out_lut_precache: V_,
        qcms_transform_data_rgba_out_lut: L_,
        qcms_transform_data_rgba_out_lut_precache: N_,
        qcms_transform_release: Y_,
        qcms_white_point_sRGB: H_,
        rust_zstd_wasm_shim_calloc: K_,
        rust_zstd_wasm_shim_free: Q_,
        rust_zstd_wasm_shim_malloc: _t,
        rust_zstd_wasm_shim_memcmp: tt,
        rust_zstd_wasm_shim_memcpy: et,
        rust_zstd_wasm_shim_memmove: rt,
        rust_zstd_wasm_shim_memset: nt,
        rust_zstd_wasm_shim_qsort: st,
        sourceconfig_new: D_,
        start: I_
    });
    h_(dt);
    D();
    let S, M;
    const ut = new Promise((t)=>{
        M = t;
    });
    self.onmessage = async (t)=>{
        const _ = t.data;
        if (_.type === "INIT") {
            console.log("Received wasm-bundle url !", _.payload.zipUrl);
            const s = await (await fetch(_.payload.zipUrl)).arrayBuffer();
            S = new E(new Uint8Array(s)), console.log("Core initialized."), M();
            return;
        }
        if (await ut, _.type === "COMPILE_CARD") {
            const e = _.payload.card;
            S.prepare_source([
                new l(e.header, e.id, e.name, e.question, e.answer, e.locations)
            ], new R(_.payload.config.pageWidth, _.payload.config.fontSize, _.payload.config.textColor, _.payload.config.useSansFont));
            const s = S.compile();
            self.postMessage({
                type: "COMPILED_CARD",
                payload: [
                    s[1].svg(),
                    s[2].svg()
                ]
            });
        }
    };
    self.postMessage({
        type: "READY",
        payload: null
    });
})();
