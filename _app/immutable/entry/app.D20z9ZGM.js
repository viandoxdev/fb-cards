const __vite__mapDeps=(i,m=__vite__mapDeps,d=(m.f||(m.f=["../nodes/0.DMkGZKur.js","../chunks/8XxP4oe4.js","../chunks/COxjHdNw.js","../chunks/C_NrtlHV.js","../chunks/lZc26GA7.js","../assets/0.DTVYy-PA.css","../nodes/1.DgcICig2.js","../chunks/Bs_1Saev.js","../chunks/BLKHoU46.js","../chunks/6Ge30gJc.js","../chunks/CnWdX46S.js","../nodes/2.Cqsq65x0.js","../chunks/Diy0Fj-1.js","../chunks/v6o6gS5i.js","../assets/cardCompiler.C4igp4C9.css","../chunks/I1RWXdXV.js","../nodes/3.Agb3371Q.js"])))=>i.map(i=>d[i]);
import { n as N, F as U, E as Y, G as J, H as K, I as W, J as X, K as D, aj as z, o as Q, A as O, X as Z, B as f, aE as $, au as ee, aF as te, p as re, aG as se, w as ae, at as ne, f as p, s as oe, a as ce, y as A, c as ie, r as ue, t as le, C as x } from "../chunks/COxjHdNw.js";
import { h as de, m as fe, u as me, s as he } from "../chunks/Bs_1Saev.js";
import { a as P, k as S, f as F, t as _e } from "../chunks/8XxP4oe4.js";
import { o as ve } from "../chunks/CnWdX46S.js";
import { p as T, i as j } from "../chunks/Diy0Fj-1.js";
import { B as ge } from "../chunks/lZc26GA7.js";
import { b as C } from "../chunks/I1RWXdXV.js";
let Ge, ke, Fe, Me, Ve, M, Ie, De, Ne, Be;
let __tla = (async ()=>{
    function L(o, e, s) {
        var u;
        N && (u = Q, U());
        var c = new ge(o);
        Y(()=>{
            var t = e() ?? null;
            if (N) {
                var r = K(u), a = r === z, E = t !== null;
                if (a !== E) {
                    var m = W();
                    X(m), c.anchor = m, D(!1), c.ensure(t, t && ((n)=>s(n, t))), D(!0);
                    return;
                }
            }
            c.ensure(t, t && ((n)=>s(n, t)));
        }, J);
    }
    function ye(o) {
        return class extends Ee {
            constructor(e){
                super({
                    component: o,
                    ...e
                });
            }
        };
    }
    class Ee {
        #t;
        #e;
        constructor(e){
            var s = new Map, u = (t, r)=>{
                var a = te(r, !1, !1);
                return s.set(t, a), a;
            };
            const c = new Proxy({
                ...e.props || {},
                $$events: {}
            }, {
                get (t, r) {
                    return f(s.get(r) ?? u(r, Reflect.get(t, r)));
                },
                has (t, r) {
                    return r === Z ? !0 : (f(s.get(r) ?? u(r, Reflect.get(t, r))), Reflect.has(t, r));
                },
                set (t, r, a) {
                    return O(s.get(r) ?? u(r, a), a), Reflect.set(t, r, a);
                }
            });
            this.#e = (e.hydrate ? de : fe)(e.component, {
                target: e.target,
                anchor: e.anchor,
                props: c,
                context: e.context,
                intro: e.intro ?? !1,
                recover: e.recover,
                transformError: e.transformError
            }), (!e?.props?.$$host || e.sync === !1) && $(), this.#t = c.$$events;
            for (const t of Object.keys(this.#e))t === "$set" || t === "$destroy" || t === "$on" || ee(this, t, {
                get () {
                    return this.#e[t];
                },
                set (r) {
                    this.#e[t] = r;
                },
                enumerable: !0
            });
            this.#e.$set = (t)=>{
                Object.assign(c, t);
            }, this.#e.$destroy = ()=>{
                me(this.#e);
            };
        }
        $set(e) {
            this.#e.$set(e);
        }
        $on(e, s) {
            this.#t[e] = this.#t[e] || [];
            const u = (...c)=>s.call(this, ...c);
            return this.#t[e].push(u), ()=>{
                this.#t[e] = this.#t[e].filter((c)=>c !== u);
            };
        }
        $destroy() {
            this.#e.$destroy();
        }
    }
    let be, Pe, B, k;
    be = "modulepreload";
    Pe = function(o, e) {
        return new URL(o, e).href;
    };
    B = {};
    k = function(e, s, u) {
        let c = Promise.resolve();
        if (s && s.length > 0) {
            let m = function(n) {
                return Promise.all(n.map((d)=>Promise.resolve(d).then((h)=>({
                            status: "fulfilled",
                            value: h
                        }), (h)=>({
                            status: "rejected",
                            reason: h
                        }))));
            };
            const r = document.getElementsByTagName("link"), a = document.querySelector("meta[property=csp-nonce]"), E = a?.nonce || a?.getAttribute("nonce");
            c = m(s.map((n)=>{
                if (n = Pe(n, u), n in B) return;
                B[n] = !0;
                const d = n.endsWith(".css"), h = d ? '[rel="stylesheet"]' : "";
                if (u) for(let _ = r.length - 1; _ >= 0; _--){
                    const i = r[_];
                    if (i.href === n && (!d || i.rel === "stylesheet")) return;
                }
                else if (document.querySelector(`link[href="${n}"]${h}`)) return;
                const l = document.createElement("link");
                if (l.rel = d ? "stylesheet" : be, d || (l.as = "script"), l.crossOrigin = "", l.href = n, E && l.setAttribute("nonce", E), document.head.appendChild(l), d) return new Promise((_, i)=>{
                    l.addEventListener("load", _), l.addEventListener("error", ()=>i(new Error(`Unable to preload CSS for ${n}`)));
                });
            }));
        }
        function t(r) {
            const a = new Event("vite:preloadError", {
                cancelable: !0
            });
            if (a.payload = r, window.dispatchEvent(a), !a.defaultPrevented) throw r;
        }
        return c.then((r)=>{
            for (const a of r || [])a.status === "rejected" && t(a.reason);
            return e().catch(t);
        });
    };
    Ie = {};
    var Re = F('<div id="svelte-announcer" aria-live="assertive" aria-atomic="true" style="position: absolute; left: 0; top: 0; clip: rect(0 0 0 0); clip-path: inset(50%); overflow: hidden; white-space: nowrap; width: 1px; height: 1px"><!></div>'), we = F("<!> <!>", 1);
    function pe(o, e) {
        re(e, !0);
        let s = T(e, "components", 23, ()=>[]), u = T(e, "data_0", 3, null), c = T(e, "data_1", 3, null);
        se(()=>e.stores.page.set(e.page)), ae(()=>{
            e.stores, e.page, e.constructors, s(), e.form, u(), c(), e.stores.page.notify();
        });
        let t = A(!1), r = A(!1), a = A(null);
        ve(()=>{
            const i = e.stores.page.subscribe(()=>{
                f(t) && (O(r, !0), ne().then(()=>{
                    O(a, document.title || "untitled page", !0);
                }));
            });
            return O(t, !0), i;
        });
        const E = x(()=>e.constructors[1]);
        var m = we(), n = p(m);
        {
            var d = (i)=>{
                const v = x(()=>e.constructors[0]);
                var g = S(), R = p(g);
                L(R, ()=>f(v), (y, b)=>{
                    C(b(y, {
                        get data () {
                            return u();
                        },
                        get form () {
                            return e.form;
                        },
                        get params () {
                            return e.page.params;
                        },
                        children: (w, Oe)=>{
                            var I = S(), V = p(I);
                            L(V, ()=>f(E), (G, q)=>{
                                C(q(G, {
                                    get data () {
                                        return c();
                                    },
                                    get form () {
                                        return e.form;
                                    },
                                    get params () {
                                        return e.page.params;
                                    }
                                }), (H)=>s()[1] = H, ()=>s()?.[1]);
                            }), P(w, I);
                        },
                        $$slots: {
                            default: !0
                        }
                    }), (w)=>s()[0] = w, ()=>s()?.[0]);
                }), P(i, g);
            }, h = (i)=>{
                const v = x(()=>e.constructors[0]);
                var g = S(), R = p(g);
                L(R, ()=>f(v), (y, b)=>{
                    C(b(y, {
                        get data () {
                            return u();
                        },
                        get form () {
                            return e.form;
                        },
                        get params () {
                            return e.page.params;
                        }
                    }), (w)=>s()[0] = w, ()=>s()?.[0]);
                }), P(i, g);
            };
            j(n, (i)=>{
                e.constructors[1] ? i(d) : i(h, -1);
            });
        }
        var l = oe(n, 2);
        {
            var _ = (i)=>{
                var v = Re(), g = ie(v);
                {
                    var R = (y)=>{
                        var b = _e();
                        le(()=>he(b, f(a))), P(y, b);
                    };
                    j(g, (y)=>{
                        f(r) && y(R);
                    });
                }
                ue(v), P(i, v);
            };
            j(l, (i)=>{
                f(t) && i(_);
            });
        }
        P(o, m), ce();
    }
    Ne = ye(pe);
    De = [
        ()=>k(()=>import("../nodes/0.DMkGZKur.js"), __vite__mapDeps([0,1,2,3,4,5]), import.meta.url),
        ()=>k(()=>import("../nodes/1.DgcICig2.js"), __vite__mapDeps([6,1,2,7,8,9,10]), import.meta.url),
        ()=>k(()=>import("../nodes/2.Cqsq65x0.js"), __vite__mapDeps([11,1,2,12,4,3,13,7,9,10,14,15,8]), import.meta.url),
        ()=>k(()=>import("../nodes/3.Agb3371Q.js"), __vite__mapDeps([16,1,2,7,12,4,13,3,9,10,14,8]), import.meta.url)
    ];
    Be = [];
    Fe = {
        "/": [
            2
        ],
        "/browse": [
            3
        ]
    };
    M = {
        handleError: (({ error: o })=>{
            console.error(o);
        }),
        reroute: (()=>{}),
        transport: {}
    };
    ke = Object.fromEntries(Object.entries(M.transport).map(([o, e])=>[
            o,
            e.decode
        ]));
    Me = Object.fromEntries(Object.entries(M.transport).map(([o, e])=>[
            o,
            e.encode
        ]));
    Ve = !1;
    Ge = (o, e)=>ke[o](e);
})();
export { Ge as decode, ke as decoders, Fe as dictionary, Me as encoders, Ve as hash, M as hooks, Ie as matchers, De as nodes, Ne as root, Be as server_loads, __tla };
