const __vite__mapDeps=(i,m=__vite__mapDeps,d=(m.f||(m.f=["../nodes/0.Czl_PERi.js","../chunks/RbMBVuNT.js","../chunks/ITZova2N.js","../chunks/CG_ykbAf.js","../chunks/wcpDxAMa.js","../assets/0.Cz4ha_M8.css","../nodes/1.BQ0geMYt.js","../chunks/DNCQndsr.js","../chunks/CL2bVApx.js","../chunks/CVSilYOI.js","../chunks/CdjkWPYO.js","../nodes/2.BRIwyijs.js","../chunks/D38o5TIy.js","../chunks/yzn4bnSo.js","../assets/cardCompiler.C4igp4C9.css","../nodes/3.CHg68YHH.js"])))=>i.map(i=>d[i]);
import { j as I, B as H, A as W, E as z, C as K, D as J, F as Q, G as B, ah as X, k as Z, n as $, aC as tt, W as et, q as rt, K as st, aD as at, T as nt, x as O, U as ot, y as h, aE as ct, ar as it, aF as ut, p as lt, aG as ft, u as dt, aH as mt, f as p, s as ht, a as _t, v as T, c as vt, r as gt, t as yt, z as S } from "../chunks/ITZova2N.js";
import { h as Et, m as bt, u as wt, s as Pt } from "../chunks/DNCQndsr.js";
import { a as w, k as x, f as F, t as Rt } from "../chunks/RbMBVuNT.js";
import { o as pt } from "../chunks/CdjkWPYO.js";
import { p as A, i as C } from "../chunks/D38o5TIy.js";
import { B as kt } from "../chunks/wcpDxAMa.js";
let Kt, jt, Ht, Wt, zt, G, Vt, qt, Yt, Ut;
let __tla = (async ()=>{
    function L(a, t, n) {
        var i;
        I && (i = Z, H());
        var c = new kt(a);
        W(()=>{
            var r = t() ?? null;
            if (I) {
                var e = K(i), s = e === X, l = r !== null;
                if (s !== l) {
                    var d = J();
                    Q(d), c.anchor = d, B(!1), c.ensure(r, r && ((o)=>n(o, r))), B(!0);
                    return;
                }
            }
            c.ensure(r, r && ((o)=>n(o, r)));
        }, z);
    }
    function j(a, t) {
        return a === t || a?.[nt] === t;
    }
    function D(a = {}, t, n, i) {
        var c = $.r, r = st;
        return tt(()=>{
            var e, s;
            return et(()=>{
                e = s, s = [], rt(()=>{
                    j(n(...s), a) || (t(a, ...s), e && j(n(...e), a) && t(null, ...e));
                });
            }), ()=>{
                let l = r;
                for(; l !== c && l.parent !== null && l.parent.f & at;)l = l.parent;
                const d = ()=>{
                    s && j(n(...s), a) && t(null, ...s);
                }, o = l.teardown;
                l.teardown = ()=>{
                    d(), o?.();
                };
            };
        }), a;
    }
    function Ot(a) {
        return class extends Tt {
            constructor(t){
                super({
                    component: a,
                    ...t
                });
            }
        };
    }
    class Tt {
        #e;
        #t;
        constructor(t){
            var n = new Map, i = (r, e)=>{
                var s = ut(e, !1, !1);
                return n.set(r, s), s;
            };
            const c = new Proxy({
                ...t.props || {},
                $$events: {}
            }, {
                get (r, e) {
                    return h(n.get(e) ?? i(e, Reflect.get(r, e)));
                },
                has (r, e) {
                    return e === ot ? !0 : (h(n.get(e) ?? i(e, Reflect.get(r, e))), Reflect.has(r, e));
                },
                set (r, e, s) {
                    return O(n.get(e) ?? i(e, s), s), Reflect.set(r, e, s);
                }
            });
            this.#t = (t.hydrate ? Et : bt)(t.component, {
                target: t.target,
                anchor: t.anchor,
                props: c,
                context: t.context,
                intro: t.intro ?? !1,
                recover: t.recover,
                transformError: t.transformError
            }), (!t?.props?.$$host || t.sync === !1) && ct(), this.#e = c.$$events;
            for (const r of Object.keys(this.#t))r === "$set" || r === "$destroy" || r === "$on" || it(this, r, {
                get () {
                    return this.#t[r];
                },
                set (e) {
                    this.#t[r] = e;
                },
                enumerable: !0
            });
            this.#t.$set = (r)=>{
                Object.assign(c, r);
            }, this.#t.$destroy = ()=>{
                wt(this.#t);
            };
        }
        $set(t) {
            this.#t.$set(t);
        }
        $on(t, n) {
            this.#e[t] = this.#e[t] || [];
            const i = (...c)=>n.call(this, ...c);
            return this.#e[t].push(i), ()=>{
                this.#e[t] = this.#e[t].filter((c)=>c !== i);
            };
        }
        $destroy() {
            this.#t.$destroy();
        }
    }
    let St, xt, M, k;
    St = "modulepreload";
    xt = function(a, t) {
        return new URL(a, t).href;
    };
    M = {};
    k = function(t, n, i) {
        let c = Promise.resolve();
        if (n && n.length > 0) {
            let d = function(o) {
                return Promise.all(o.map((m)=>Promise.resolve(m).then((_)=>({
                            status: "fulfilled",
                            value: _
                        }), (_)=>({
                            status: "rejected",
                            reason: _
                        }))));
            };
            const e = document.getElementsByTagName("link"), s = document.querySelector("meta[property=csp-nonce]"), l = s?.nonce || s?.getAttribute("nonce");
            c = d(n.map((o)=>{
                if (o = xt(o, i), o in M) return;
                M[o] = !0;
                const m = o.endsWith(".css"), _ = m ? '[rel="stylesheet"]' : "";
                if (i) for(let v = e.length - 1; v >= 0; v--){
                    const u = e[v];
                    if (u.href === o && (!m || u.rel === "stylesheet")) return;
                }
                else if (document.querySelector(`link[href="${o}"]${_}`)) return;
                const f = document.createElement("link");
                if (f.rel = m ? "stylesheet" : St, m || (f.as = "script"), f.crossOrigin = "", f.href = o, l && f.setAttribute("nonce", l), document.head.appendChild(f), m) return new Promise((v, u)=>{
                    f.addEventListener("load", v), f.addEventListener("error", ()=>u(new Error(`Unable to preload CSS for ${o}`)));
                });
            }));
        }
        function r(e) {
            const s = new Event("vite:preloadError", {
                cancelable: !0
            });
            if (s.payload = e, window.dispatchEvent(s), !s.defaultPrevented) throw e;
        }
        return c.then((e)=>{
            for (const s of e || [])s.status === "rejected" && r(s.reason);
            return t().catch(r);
        });
    };
    Vt = {};
    var At = F('<div id="svelte-announcer" aria-live="assertive" aria-atomic="true" style="position: absolute; left: 0; top: 0; clip: rect(0 0 0 0); clip-path: inset(50%); overflow: hidden; white-space: nowrap; width: 1px; height: 1px"><!></div>'), Ct = F("<!> <!>", 1);
    function Lt(a, t) {
        lt(t, !0);
        let n = A(t, "components", 23, ()=>[]), i = A(t, "data_0", 3, null), c = A(t, "data_1", 3, null);
        ft(()=>t.stores.page.set(t.page)), dt(()=>{
            t.stores, t.page, t.constructors, n(), t.form, i(), c(), t.stores.page.notify();
        });
        let r = T(!1), e = T(!1), s = T(null);
        pt(()=>{
            const u = t.stores.page.subscribe(()=>{
                h(r) && (O(e, !0), mt().then(()=>{
                    O(s, document.title || "untitled page", !0);
                }));
            });
            return O(r, !0), u;
        });
        const l = S(()=>t.constructors[1]);
        var d = Ct(), o = p(d);
        {
            var m = (u)=>{
                const g = S(()=>t.constructors[0]);
                var y = x(), P = p(y);
                L(P, ()=>h(g), (E, b)=>{
                    D(b(E, {
                        get data () {
                            return i();
                        },
                        get form () {
                            return t.form;
                        },
                        get params () {
                            return t.page.params;
                        },
                        children: (R, Dt)=>{
                            var N = x(), V = p(N);
                            L(V, ()=>h(l), (Y, q)=>{
                                D(q(Y, {
                                    get data () {
                                        return c();
                                    },
                                    get form () {
                                        return t.form;
                                    },
                                    get params () {
                                        return t.page.params;
                                    }
                                }), (U)=>n()[1] = U, ()=>n()?.[1]);
                            }), w(R, N);
                        },
                        $$slots: {
                            default: !0
                        }
                    }), (R)=>n()[0] = R, ()=>n()?.[0]);
                }), w(u, y);
            }, _ = (u)=>{
                const g = S(()=>t.constructors[0]);
                var y = x(), P = p(y);
                L(P, ()=>h(g), (E, b)=>{
                    D(b(E, {
                        get data () {
                            return i();
                        },
                        get form () {
                            return t.form;
                        },
                        get params () {
                            return t.page.params;
                        }
                    }), (R)=>n()[0] = R, ()=>n()?.[0]);
                }), w(u, y);
            };
            C(o, (u)=>{
                t.constructors[1] ? u(m) : u(_, -1);
            });
        }
        var f = ht(o, 2);
        {
            var v = (u)=>{
                var g = At(), y = vt(g);
                {
                    var P = (E)=>{
                        var b = Rt();
                        yt(()=>Pt(b, h(s))), w(E, b);
                    };
                    C(y, (E)=>{
                        h(e) && E(P);
                    });
                }
                gt(g), w(u, g);
            };
            C(f, (u)=>{
                h(r) && u(v);
            });
        }
        w(a, d), _t();
    }
    Yt = Ot(Lt);
    qt = [
        ()=>k(()=>import("../nodes/0.Czl_PERi.js"), __vite__mapDeps([0,1,2,3,4,5]), import.meta.url),
        ()=>k(()=>import("../nodes/1.BQ0geMYt.js"), __vite__mapDeps([6,1,2,7,8,9,10]), import.meta.url),
        ()=>k(()=>import("../nodes/2.BRIwyijs.js"), __vite__mapDeps([11,1,2,12,4,3,13,7,9,10,14,8]), import.meta.url),
        ()=>k(()=>import("../nodes/3.CHg68YHH.js"), __vite__mapDeps([15,1,2,7,12,4,13,3,9,10,14,8]), import.meta.url)
    ];
    Ut = [];
    Ht = {
        "/": [
            2
        ],
        "/browse": [
            3
        ]
    };
    G = {
        handleError: (({ error: a })=>{
            console.error(a);
        }),
        reroute: (()=>{}),
        transport: {}
    };
    jt = Object.fromEntries(Object.entries(G.transport).map(([a, t])=>[
            a,
            t.decode
        ]));
    Wt = Object.fromEntries(Object.entries(G.transport).map(([a, t])=>[
            a,
            t.encode
        ]));
    zt = !1;
    Kt = (a, t)=>jt[a](t);
})();
export { Kt as decode, jt as decoders, Ht as dictionary, Wt as encoders, zt as hash, G as hooks, Vt as matchers, qt as nodes, Yt as root, Ut as server_loads, __tla };
