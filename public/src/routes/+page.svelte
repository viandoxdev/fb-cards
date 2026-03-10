<script lang="ts">
    import { PUBLIC_CACHE_BUSTER } from '$env/static/public';
    import MaterialSymbolsNoteStackOutline from "~icons/material-symbols/note-stack-outline";
    import MaterialSymbolsSettings from "~icons/material-symbols/settings";
    import MaterialSymbolsCloseRounded from "~icons/material-symbols/close-rounded";
    import SearchBar from "$lib/SearchBar.svelte";
    import _cards from "$lib/cards.json";
    import type { WorkerRequests, WorkerResponse } from "$lib/wasm-worker";
    import WasmWorker from "$lib/wasm-worker.ts?worker";
    import { onDestroy, onMount } from "svelte";
    import uFuzzy from "@leeoniya/ufuzzy";
    import type { Card } from "../app";
    import Popup from "$lib/Popup.svelte";
    import Loader from "$lib/Loader.svelte";

    const cards = _cards as Card[];

    let worker: Worker | undefined;
    let query = $state("");
    let settingsOpen = $state(false);
    let fontSize = $state(20);
    let useSansFont = $state(false);
    let pageWidth = $state(0);
    let frontSvg = $state("");
    let backSvg = $state("");
    let cardOpen = $state(false);
    let cardName = $state("");
    let isLoading = $state(false);

    const uf = new uFuzzy();
    const haystack = cards.map((item) => item.name);

    const results = $derived.by(() => {
        const max_results = 20;

        if (query.trim().length == 0) {
            return cards.slice(0, max_results - 1);
        }

        const [idxs, info, order] = uf.search(haystack, query);

        if (!idxs || !info || !order || order.length == 0) return [];

        return order.slice(0, max_results - 1).map((i) => cards[info.idx[i]]);
    });

    onMount(async () => {
        worker = new WasmWorker();

        worker.onmessage = (event) => {
            const message = event.data as WorkerResponse;

            switch (message.type) {
                case "COMPILED_CARD":
                    isLoading = false;
                    cardOpen = true;
                    frontSvg = message.payload[0];
                    backSvg = message.payload[1];
                    break;
            }
        };
    });

    function renderCard(card: Card) {
        cardName = card.name;
        isLoading = true;
        sendMessage({
            type: "COMPILE_CARD",
            payload: {
                card: card,
                config: { fontSize, pageWidth, useSansFont, textColor: 0 },
            },
        });
    }

    function sendMessage(message: WorkerRequests) {
        worker?.postMessage(message);
    }

    onDestroy(() => {
        if (worker) worker.terminate();
    });
</script>

<div
    class="w-screen p-0 grow-1 overflow-hidden flex flex-col"
    bind:clientWidth={pageWidth}
>
    <div
        class="w-full bg-white flex h-16 min-h-16 items-center justify-between px-4 sm:px-6 lg:px-8"
    >
        <div
            class="flex items-center text-xl font-bold tracking-tight text-slate-900"
        >
            Flashbang cards
        </div>

        <div class="flex items-center gap-x-3">
            <button
                class="rounded-md p-2 hover:bg-slate-100 text-slate-900 cursor-pointer transition-colors"
                onclick={() => (settingsOpen = true)}
            >
                <MaterialSymbolsSettings />
            </button>

            <a
                class="rounded-md p-2 bg-indigo-400 hover:bg-indigo-500 transition-colors text-white font-bold"
                href="_full.pdf?v={PUBLIC_CACHE_BUSTER}"
            >
                full PDF
            </a>
        </div>
    </div>

    {#if !cardOpen && !isLoading}
        <SearchBar bind:query {results} select={renderCard} />
    {/if}

    {#if isLoading}
        <div class="flex grow-2 flex-col items-center justify-center">
            <Loader />
        </div>
    {/if}

    {#if cardOpen}
        <div
            class="w-full min-h-1 grow-2 bg-slate-200 flex flex-col overflow-scroll"
        >
            <div class="flex flex-col p-3 m-3 rounded-xl bg-white">
                <div class="flex flex-row gap-4 items-center p-2">
                    <MaterialSymbolsNoteStackOutline class="min-w-6 min-h-6" />
                    <span class="grow-1 text-xl font-bold text-left"
                        >{cardName}</span
                    >
                    <button
                        onclick={() => (cardOpen = false)}
                        aria-label="Close popup"
                    >
                        <MaterialSymbolsCloseRounded class="min-w-6 min-h-6" />
                    </button>
                </div>
                <div
                    class="w-full flex justify-center [&>svg]:max-w-full [&>svg]:h-auto"
                >
                    {@html frontSvg}
                </div>
                <div
                    class="w-full flex justify-center [&>svg]:max-w-full [&>svg]:h-auto"
                >
                    {@html backSvg}
                </div>
            </div>
        </div>
    {/if}

    {#if settingsOpen}
        <Popup title="Settings" onclose={() => (settingsOpen = false)}>
            <div class="flex flex-col p-1">
                <div class="flex flex-row justify-between">
                    <label for="font_size" class="font-bold mb-2"
                        >Font size</label
                    >
                    <span> {fontSize} </span>
                </div>
                <input
                    id="font_size"
                    bind:value={fontSize}
                    type="range"
                    min="0"
                    max="40"
                />
                <div class="flex flex-row justify-between mt-3">
                    <label for="sans" class="font-bold mb-2"
                        >Sans math font</label
                    >
                    <input
                        id="sans"
                        type="checkbox"
                        bind:checked={useSansFont}
                    />
                </div>
            </div>
        </Popup>
    {/if}
</div>
