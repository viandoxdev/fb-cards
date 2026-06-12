<script lang="ts">
    import { PUBLIC_CACHE_BUSTER } from '$env/static/public';
    import MaterialSymbolsSettings from "~icons/material-symbols/settings";
    import MaterialSymbolsFolderOpenOutline from "~icons/material-symbols/folder-open-outline";
    import SearchBar, { type SearchResult } from "$lib/SearchBar.svelte";
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

    const uf = new uFuzzy({ interIns: Infinity });
    const foldedNames = uFuzzy.latinize(cards.map((c) => c.name));
    const haystack = cards.map(
        (c, i) =>
            foldedNames[i] +
            " " +
            uFuzzy.latinize(c.locations).join(" ").replace(/\./g, " "),
    );
    const foldedBodies = uFuzzy.latinize(
        cards.map((c) => c.search_body ?? ""),
    );

    const MAX_RESULTS = 20;
    const SNIPPET_LEN = 90;

    function asResult(
        card: Card,
        nameRanges: number[] = [],
        bodySnippet?: SearchResult["bodySnippet"],
    ): SearchResult {
        return { card, nameRanges, bodySnippet };
    }

    function makeBodySnippet(
        originalBody: string,
        ranges: number[],
    ): SearchResult["bodySnippet"] {
        if (!ranges || ranges.length < 2) return undefined;
        const firstStart = ranges[0];
        const firstEnd = ranges[1];
        const matchLen = firstEnd - firstStart;
        const pad = Math.max(0, Math.floor((SNIPPET_LEN - matchLen) / 2));
        let start = Math.max(0, firstStart - pad);
        let end = Math.min(originalBody.length, start + SNIPPET_LEN);
        start = Math.max(0, end - SNIPPET_LEN);
        // Pull back to the previous whitespace so we don't slice through a word.
        while (start > 0 && !/\s/.test(originalBody[start - 1])) start--;
        const prefix = start > 0 ? "…" : "";
        const suffix = end < originalBody.length ? "…" : "";
        const shift = prefix.length - start;
        const localRanges: number[] = [];
        for (let i = 0; i < ranges.length; i += 2) {
            const s = ranges[i];
            const e = ranges[i + 1];
            if (e <= start || s >= end) continue;
            localRanges.push(
                Math.max(start, s) + shift,
                Math.min(end, e) + shift,
            );
        }
        return {
            text: prefix + originalBody.slice(start, end) + suffix,
            ranges: localRanges,
        };
    }

    const results = $derived.by<SearchResult[]>(() => {
        const trimmed = query.trim();
        if (trimmed.length === 0) {
            return cards.slice(0, MAX_RESULTS).map((c) => asResult(c));
        }

        const needle = uFuzzy.latinize(trimmed);

        // Tier 1: name + locations.
        const out: SearchResult[] = [];
        const seen = new Set<number>();
        const [nIdxs, nInfo, nOrder] = uf.search(haystack, needle, 5);
        if (nIdxs && nInfo && nOrder) {
            for (const orderIdx of nOrder) {
                const matchIdx = nInfo.idx[orderIdx];
                seen.add(matchIdx);
                if (out.length >= MAX_RESULTS) continue;
                const card = cards[matchIdx];
                const nameLen = foldedNames[matchIdx].length;
                const ranges = nInfo.ranges[orderIdx] ?? [];
                const clipped: number[] = [];
                for (let i = 0; i < ranges.length; i += 2) {
                    const s = ranges[i];
                    if (s >= nameLen) break;
                    clipped.push(s, Math.min(ranges[i + 1], nameLen));
                }
                out.push(asResult(card, clipped));
            }
        }
        if (out.length >= MAX_RESULTS) return out;

        // Tier 2: body text, skipping cards already shown above.
        const [bIdxs, bInfo, bOrder] = uf.search(foldedBodies, needle, 5);
        if (bIdxs && bInfo && bOrder) {
            for (const orderIdx of bOrder) {
                if (out.length >= MAX_RESULTS) break;
                const matchIdx = bInfo.idx[orderIdx];
                if (seen.has(matchIdx)) continue;
                const card = cards[matchIdx];
                const body = card.search_body ?? "";
                const snippet = makeBodySnippet(
                    body,
                    bInfo.ranges[orderIdx] ?? [],
                );
                out.push(asResult(card, [], snippet));
            }
        }
        return out;
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
