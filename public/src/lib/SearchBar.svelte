<script lang="ts">
    import MaterialSymbolsSearch from '~icons/material-symbols/search'
    import MaterialSymbolsCloseRounded from '~icons/material-symbols/close-rounded'
    import { fade } from "svelte/transition";
    import type { Card } from "../app";

    let expanded = false;
    export let query = "";
    export let results: Card[] = [];
    export let select: (card: Card) => void = (_) => {};

    function expand() {
        expanded = true;
    }

    function collapse() {
        expanded = false;
        query = ""; // Optional: clear search on close
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
                onclick={collapse}
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
                            onclick={() => {
                                collapse();
                                select(result);
                            }}>{result.name}</button
                        >
                    </li>
                {:else}
                    <li class="w-full p-3 text-center text-slate-500">No results found for "{query}"</li>
                {/each}
            </ul>
        </div>
    {/if}
</div>
