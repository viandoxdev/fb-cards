<script lang="ts">
    import MaterialSymbolsSearch from '~icons/material-symbols/search'
    import MaterialSymbolsCloseRounded from '~icons/material-symbols/close-rounded'
    import { fade } from "svelte/transition";
    import { onMount } from "svelte";
    import type { Card } from "../app";

    let expanded = $state(false);
    let {
        query = $bindable(""),
        results = [],
        select = (_: Card) => {},
    }: {
        query?: string;
        results?: Card[];
        select?: (card: Card) => void;
    } = $props();

    onMount(() => {
        // If a query was preserved (e.g. by history navigation), open the
        // results view immediately rather than showing the placeholder.
        if (query) expanded = true;
    });

    function expand() {
        expanded = true;
    }

    function dismiss() {
        expanded = false;
        query = "";
    }
</script>

<div class="size-full flex flex-col overflow-hidden ">
    <div class="p-3 my-3 flex flex-row items-center gap-2 transition-all {expanded ? 'mx-0' : 'rounded-xl mx-3 bg-slate-200'}">
        <div class="search-icon">
            <MaterialSymbolsSearch class={expanded ? 'text-slate-700' : 'text-slate-500'} />
        </div>

        <input
            class="grow-2 outline-0"
            type="text"
            placeholder="Search..."
            bind:value={query}
            onfocus={expand}
        />

        {#if expanded}
            <button
                onclick={dismiss}
                transition:fade={{ duration: 150 }}
            >
                <MaterialSymbolsCloseRounded />

            </button>
        {/if}
    </div>

    {#if expanded}
        <div class="flex flex-col overflow-scroll flex-1" transition:fade={{ duration: 200 }}>
            <ul>
                {#each results as result}
                    <li>
                        <button class="p-3 size-full text-left hover:bg-slate-200 transition-colors cursor-pointer"
                            onclick={() => select(result)}>{result.name}</button
                        >
                    </li>
                {:else}
                    <li class="w-full p-3 text-center text-slate-500">No results found for "{query}"</li>
                {/each}
            </ul>
        </div>
    {:else}
        <div class="flex flex-col items-center justify-center grow-1 gap-4 px-6 pb-8 text-center select-none">
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
        </div>
    {/if}
</div>
