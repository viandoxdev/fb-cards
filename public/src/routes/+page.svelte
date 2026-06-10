<script lang="ts">
    import { PUBLIC_CACHE_BUSTER } from '$env/static/public';
    import MaterialSymbolsSettings from "~icons/material-symbols/settings";
    import MaterialSymbolsFolderOpenOutline from "~icons/material-symbols/folder-open-outline";
    import SearchBar from "$lib/SearchBar.svelte";
    import _cards from "$lib/cards.json";
    import uFuzzy from "@leeoniya/ufuzzy";
    import type { Card } from "../app";
    import Loader from "$lib/Loader.svelte";
    import CardPreview from "$lib/CardPreview.svelte";
    import SettingsPopup from "$lib/SettingsPopup.svelte";
    import { compileCard } from "$lib/cardCompiler";
    import { settings } from "$lib/settings.svelte";
    import { pushState, replaceState } from "$app/navigation";
    import { page } from "$app/state";

    type SearchState = {
        kind: "search";
        query: string;
        cardId: string | null;
    };

    const cards = _cards as Card[];

    let query = $state("");
    let settingsOpen = $state(false);
    let pageWidth = $state(0);
    let frontSvg = $state("");
    let backSvg = $state("");
    let cardOpen = $state(false);
    let cardName = $state("");
    let isLoading = $state(false);

    let activeCardId: string | null = null;
    let renderSeq = 0;

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

    function renderCard(card: Card) {
        // Snapshot the current query into the entry we're leaving so back
        // restores it, then push a new entry representing the preview.
        replaceState("", {
            kind: "search",
            query,
            cardId: null,
        } satisfies SearchState);
        pushState("", {
            kind: "search",
            query,
            cardId: card.id,
        } satisfies SearchState);
    }

    async function loadCard(card: Card) {
        cardName = card.name;
        isLoading = true;
        cardOpen = false;
        const seq = ++renderSeq;
        const [front, back] = await compileCard(card, {
            fontSize: settings.fontSize,
            pageWidth,
            useSansFont: settings.useSansFont,
            textColor: 0,
        });
        if (seq !== renderSeq) return;
        frontSvg = front;
        backSvg = back;
        isLoading = false;
        cardOpen = true;
    }

    $effect(() => {
        const state = page.state as Partial<SearchState> | undefined;
        const isOurs = state?.kind === "search";
        const newCardId = isOurs ? (state.cardId ?? null) : null;

        if (newCardId === activeCardId) return;
        activeCardId = newCardId;
        renderSeq++;

        if (newCardId === null) {
            cardOpen = false;
            isLoading = false;
            // Restore the query that was active when this entry was created.
            if (isOurs && state.query !== undefined && state.query !== query) {
                query = state.query;
            }
        } else {
            const card = cards.find((c) => c.id === newCardId);
            if (card) loadCard(card);
        }
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
            <a
                class="rounded-md p-2 hover:bg-slate-100 text-slate-900 cursor-pointer transition-colors"
                href="browse"
                aria-label="Browse cards"
            >
                <MaterialSymbolsFolderOpenOutline />
            </a>

            <button
                class="rounded-md p-2 hover:bg-slate-100 text-slate-900 cursor-pointer transition-colors"
                onclick={() => (settingsOpen = true)}
                aria-label="Settings"
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
        <CardPreview
            {cardName}
            {frontSvg}
            {backSvg}
            onclose={() => history.back()}
        />
    {/if}

    {#if settingsOpen}
        <SettingsPopup onclose={() => (settingsOpen = false)} />
    {/if}
</div>
