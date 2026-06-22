<script lang="ts">
    import { PUBLIC_CACHE_BUSTER } from "$env/static/public";
    import MaterialSymbolsSettings from "~icons/material-symbols/settings";
    import MaterialSymbolsSearch from "~icons/material-symbols/search";
    import MaterialSymbolsFolderOutline from "~icons/material-symbols/folder-outline";
    import MaterialSymbolsNoteStackOutline from "~icons/material-symbols/note-stack-outline";
    import MaterialSymbolsChevronRight from "~icons/material-symbols/chevron-right";
    import _cards from "$lib/cards.json";
    import type { Card } from "../../app";
    import Loader from "$lib/Loader.svelte";
    import CardPreview from "$lib/CardPreview.svelte";
    import SettingsPopup from "$lib/SettingsPopup.svelte";
    import { compileCard } from "$lib/cardCompiler";
    import { settings } from "$lib/settings.svelte";
    import { pushState } from "$app/navigation";
    import { page } from "$app/state";

    type BrowseState = {
        kind: "browse";
        path: string[];
        cardId: string | null;
    };

    type TreeNode = {
        name: string;
        fullPath: string;
        children: Map<string, TreeNode>;
        cards: Card[];
        indirectCount: number;
    };

    const cards = _cards as Card[];

    function buildTree(): TreeNode {
        const root: TreeNode = {
            name: "",
            fullPath: "",
            children: new Map(),
            cards: [],
            indirectCount: 0,
        };

        for (const card of cards) {
            for (const loc of card.locations) {
                if (!loc) continue;
                const parts = loc.split(".");
                let cur = root;
                for (const part of parts) {
                    let child = cur.children.get(part);
                    if (!child) {
                        child = {
                            name: part,
                            fullPath: cur.fullPath
                                ? `${cur.fullPath}.${part}`
                                : part,
                            children: new Map(),
                            cards: [],
                            indirectCount: 0,
                        };
                        cur.children.set(part, child);
                    }
                    cur = child;
                }
                cur.cards.push(card);
            }
        }

        function compute(node: TreeNode): Set<string> {
            const ids = new Set<string>();
            for (const card of node.cards) ids.add(card.id);
            for (const child of node.children.values()) {
                for (const id of compute(child)) ids.add(id);
            }
            node.indirectCount = ids.size;
            return ids;
        }
        compute(root);

        return root;
    }

    const root = buildTree();

    let path = $state<string[]>([]);
    let settingsOpen = $state(false);
    let pageWidth = $state(0);

    let frontSvg = $state("");
    let backSvg = $state("");
    let cardOpen = $state(false);
    let cardName = $state("");
    let isLoading = $state(false);

    let activeCardId: string | null = null;
    let renderSeq = 0;

    const currentNode = $derived.by(() => {
        let cur = root;
        for (const seg of path) {
            const next = cur.children.get(seg);
            if (!next) return cur;
            cur = next;
        }
        return cur;
    });

    const sortedDirs = $derived(
        [...currentNode.children.values()].sort((a, b) =>
            a.name.localeCompare(b.name),
        ),
    );

    const sortedCards = $derived(
        [...currentNode.cards].sort((a, b) => a.name.localeCompare(b.name)),
    );

    function enter(name: string) {
        pushState("", {
            kind: "browse",
            path: [...path, name],
            cardId: null,
        } satisfies BrowseState);
    }

    function goTo(index: number) {
        pushState("", {
            kind: "browse",
            path: path.slice(0, index),
            cardId: null,
        } satisfies BrowseState);
    }

    function renderCard(card: Card) {
        pushState("", {
            kind: "browse",
            path: [...path],
            cardId: card.id,
        } satisfies BrowseState);
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
        const state = page.state as Partial<BrowseState> | undefined;
        const isOurs = state?.kind === "browse";
        const targetPath = isOurs ? (state.path ?? []) : [];
        const newCardId = isOurs ? (state.cardId ?? null) : null;

        const pathChanged =
            targetPath.length !== path.length ||
            targetPath.some((s, i) => s !== path[i]);
        if (pathChanged) path = targetPath;

        if (newCardId === activeCardId) return;
        activeCardId = newCardId;
        renderSeq++;

        if (newCardId === null) {
            cardOpen = false;
            isLoading = false;
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
                href="./"
                aria-label="Search cards"
            >
                <MaterialSymbolsSearch />
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

    {#if isLoading}
        <div class="flex grow-2 flex-col items-center justify-center">
            <Loader />
        </div>
    {:else if cardOpen}
        <CardPreview
            {cardName}
            {frontSvg}
            {backSvg}
            onclose={() => history.back()}
        />
    {:else}
        <div class="w-full grow-1 min-h-1 flex flex-col overflow-hidden">
            <div
                class="px-4 sm:px-6 lg:px-8 py-3 flex flex-wrap items-center gap-1 text-sm text-slate-600 border-b border-slate-200"
            >
                <button
                    class="cursor-pointer hover:text-slate-900 font-medium {path.length ===
                    0
                        ? 'text-slate-900'
                        : ''}"
                    onclick={() => goTo(0)}
                >
                    Browse
                </button>
                {#each path as seg, i}
                    <MaterialSymbolsChevronRight class="text-slate-400" />
                    <button
                        class="cursor-pointer hover:text-slate-900 {i ===
                        path.length - 1
                            ? 'font-medium text-slate-900'
                            : ''}"
                        onclick={() => goTo(i + 1)}
                    >
                        {seg}
                    </button>
                {/each}
            </div>

            <div
                class="flex-1 overflow-y-auto px-4 sm:px-6 lg:px-8 pt-2 pb-24 sm:pb-6"
            >
                {#if sortedDirs.length === 0 && sortedCards.length === 0}
                    <div class="text-center text-slate-500 py-8">
                        Nothing here.
                    </div>
                {/if}

                <ul>
                    {#each sortedDirs as dir (dir.fullPath)}
                        <li>
                            <button
                                class="w-full flex items-center gap-3 p-3 rounded-lg hover:bg-slate-100 transition-colors cursor-pointer text-left"
                                onclick={() => enter(dir.name)}
                            >
                                <MaterialSymbolsFolderOutline
                                    class="min-w-5 min-h-5 text-indigo-500"
                                />
                                <span class="grow-1 font-medium text-slate-900">
                                    {dir.name}
                                </span>
                                <span class="text-sm text-slate-500">
                                    {dir.indirectCount}
                                </span>
                                <MaterialSymbolsChevronRight
                                    class="text-slate-400"
                                />
                            </button>
                        </li>
                    {/each}

                    {#each sortedCards as card (card.id)}
                        <li>
                            <button
                                class="w-full flex items-center gap-3 p-3 rounded-lg hover:bg-slate-100 transition-colors cursor-pointer text-left"
                                onclick={() => renderCard(card)}
                            >
                                <MaterialSymbolsNoteStackOutline
                                    class="min-w-5 min-h-5 text-slate-600"
                                />
                                <span class="grow-1 text-slate-900">
                                    {card.name}
                                </span>
                            </button>
                        </li>
                    {/each}
                </ul>
            </div>
        </div>
    {/if}

    {#if settingsOpen}
        <SettingsPopup onclose={() => (settingsOpen = false)} />
    {/if}
</div>
