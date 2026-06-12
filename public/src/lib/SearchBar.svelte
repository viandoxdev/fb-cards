<script lang="ts" module>
    import type { Card } from "../app";
    export type SearchResult = {
        card: Card;
        nameRanges: number[];
        bodySnippet?: {
            text: string;
            ranges: number[];
        };
    };
</script>

<script lang="ts">
    import MaterialSymbolsSearch from '~icons/material-symbols/search'
    import MaterialSymbolsCloseRounded from '~icons/material-symbols/close-rounded'
    import uFuzzy from "@leeoniya/ufuzzy";
    import { fade } from "svelte/transition";
    import { onMount, tick } from "svelte";

    let expanded = $state(false);
    let inputEl: HTMLInputElement | undefined = $state();
    let listEl: HTMLUListElement | undefined = $state();
    let selectedIndex = $state(0);

    let {
        query = $bindable(""),
        results = [],
        select = (_: Card) => {},
    }: {
        query?: string;
        results?: SearchResult[];
        select?: (card: Card) => void;
    } = $props();

    onMount(() => {
        if (query) expanded = true;

        function onGlobalKey(e: KeyboardEvent) {
            if (e.key !== "/" || e.ctrlKey || e.metaKey || e.altKey) return;
            const t = e.target as HTMLElement | null;
            if (
                t?.tagName === "INPUT" ||
                t?.tagName === "TEXTAREA" ||
                t?.isContentEditable
            )
                return;
            e.preventDefault();
            inputEl?.focus();
        }
        window.addEventListener("keydown", onGlobalKey);
        return () => window.removeEventListener("keydown", onGlobalKey);
    });

    // Clamp selection whenever the result set changes.
    $effect(() => {
        const len = results.length;
        if (selectedIndex >= len) selectedIndex = 0;
    });

    function expand() {
        expanded = true;
    }

    function dismiss() {
        expanded = false;
        query = "";
        selectedIndex = 0;
    }

    function scrollSelectedIntoView() {
        tick().then(() => {
            listEl
                ?.querySelector<HTMLElement>(`[data-idx="${selectedIndex}"]`)
                ?.scrollIntoView({ block: "nearest" });
        });
    }

    function onInputKeydown(e: KeyboardEvent) {
        if (e.key === "ArrowDown") {
            e.preventDefault();
            if (results.length === 0) return;
            selectedIndex = (selectedIndex + 1) % results.length;
            scrollSelectedIntoView();
        } else if (e.key === "ArrowUp") {
            e.preventDefault();
            if (results.length === 0) return;
            selectedIndex =
                (selectedIndex - 1 + results.length) % results.length;
            scrollSelectedIntoView();
        } else if (e.key === "Enter") {
            if (results.length === 0) return;
            e.preventDefault();
            select(results[selectedIndex].card);
        } else if (e.key === "Escape") {
            e.preventDefault();
            if (query.length > 0) {
                query = "";
            } else {
                inputEl?.blur();
                dismiss();
            }
        }
    }

    type Segment = { text: string; matched: boolean };

    function highlight(name: string, ranges: number[]): Segment[] {
        if (!ranges || ranges.length === 0) return [{ text: name, matched: false }];
        return uFuzzy.highlight<Segment[], Segment>(
            name,
            ranges,
            (text, matched) => ({ text, matched }),
            [],
            (acc, part) => {
                acc.push(part);
                return acc;
            },
        );
    }

    function breadcrumb(card: Card): string {
        const loc = card.locations[0];
        if (!loc) return "";
        return loc.split(".").join(" › ");
    }
</script>

<div class="size-full flex flex-col overflow-hidden">
    <div
        class="p-3 my-3 flex flex-row items-center gap-2 transition-all {expanded
            ? 'mx-0'
            : 'rounded-xl mx-3 bg-slate-200'}"
    >
        <div class="search-icon">
            <MaterialSymbolsSearch
                class={expanded ? "text-slate-700" : "text-slate-500"}
            />
        </div>

        <input
            bind:this={inputEl}
            class="grow-2 outline-0"
            type="text"
            placeholder="Search..."
            bind:value={query}
            onfocus={expand}
            onkeydown={onInputKeydown}
        />

        {#if expanded}
            <button onclick={dismiss} transition:fade={{ duration: 150 }}>
                <MaterialSymbolsCloseRounded />
            </button>
        {/if}
    </div>

    {#if expanded}
        <div
            class="flex flex-col overflow-scroll flex-1"
            transition:fade={{ duration: 200 }}
        >
            <ul bind:this={listEl}>
                {#each results as result, i (result.card.id)}
                    {@const segments = highlight(
                        result.card.name,
                        result.nameRanges,
                    )}
                    {@const crumb = breadcrumb(result.card)}
                    {@const snippetSegments = result.bodySnippet
                        ? highlight(
                              result.bodySnippet.text,
                              result.bodySnippet.ranges,
                          )
                        : null}
                    <li>
                        <button
                            data-idx={i}
                            class="p-3 size-full text-left transition-colors cursor-pointer flex flex-col gap-0.5 {i ===
                            selectedIndex
                                ? 'bg-slate-200'
                                : 'hover:bg-slate-100'}"
                            onclick={() => select(result.card)}
                            onmouseenter={() => (selectedIndex = i)}
                        >
                            <span class="text-slate-900">
                                {#each segments as seg}{#if seg.matched}<mark
                                            class="bg-indigo-100 text-indigo-900 rounded-sm px-0.5"
                                            >{seg.text}</mark
                                        >{:else}{seg.text}{/if}{/each}
                            </span>
                            {#if crumb}
                                <span
                                    class="text-xs text-slate-500 flex items-center"
                                >
                                    {crumb}
                                </span>
                            {/if}
                            {#if snippetSegments}
                                <span
                                    class="text-xs text-slate-500 italic mt-0.5 line-clamp-2"
                                >
                                    {#each snippetSegments as seg}{#if seg.matched}<mark
                                                class="bg-indigo-100 text-indigo-900 rounded-sm px-0.5 not-italic"
                                                >{seg.text}</mark
                                            >{:else}{seg.text}{/if}{/each}
                                </span>
                            {/if}
                        </button>
                    </li>
                {:else}
                    <li class="w-full p-3 text-center text-slate-500">
                        No results found for "{query}"
                    </li>
                {/each}
            </ul>
        </div>
    {:else}
        <div
            class="flex flex-col items-center justify-center grow-1 gap-4 px-6 pb-8 text-center select-none"
        >
            <svg
                viewBox="0 0 200 200"
                xmlns="http://www.w3.org/2000/svg"
                class="w-40 h-40 sm:w-56 sm:h-56"
                aria-hidden="true"
            >
                <g transform="translate(100 105)">
                    <g transform="rotate(-14)">
                        <rect x="-58" y="-38" width="116" height="76" rx="10" fill="#e0e7ff" stroke="#c7d2fe" stroke-width="2" />
                    </g>
                    <g transform="rotate(-4)">
                        <rect x="-58" y="-38" width="116" height="76" rx="10" fill="#eef2ff" stroke="#c7d2fe" stroke-width="2" />
                    </g>
                    <g transform="rotate(8)">
                        <rect x="-58" y="-38" width="116" height="76" rx="10" fill="#ffffff" stroke="#a5b4fc" stroke-width="2" />
                        <rect x="-42" y="-22" width="64" height="6" rx="3" fill="#a5b4fc" />
                        <rect x="-42" y="-8" width="84" height="5" rx="2.5" fill="#e0e7ff" />
                        <rect x="-42" y="4" width="76" height="5" rx="2.5" fill="#e0e7ff" />
                        <rect x="-42" y="16" width="40" height="5" rx="2.5" fill="#e0e7ff" />
                    </g>
                </g>
                <g transform="translate(146 152)">
                    <circle cx="0" cy="0" r="18" fill="none" stroke="#6366f1" stroke-width="5" />
                    <line x1="13" y1="13" x2="26" y2="26" stroke="#6366f1" stroke-width="5" stroke-linecap="round" />
                </g>
            </svg>
            <p class="text-slate-500 text-lg">Search a card to get started.</p>
            <p class="text-slate-400 text-xs">
                Press <kbd class="px-1.5 py-0.5 rounded bg-slate-100 border border-slate-300 font-mono">/</kbd> to focus search
            </p>
        </div>
    {/if}
</div>
