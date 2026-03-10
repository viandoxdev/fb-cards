<script lang="ts">
    import type { Snippet } from "svelte";
    import { fade } from "svelte/transition";
    import MaterialSymbolsCloseRounded from "~icons/material-symbols/close-rounded";

    // Define our Svelte 5 props
    let {
        title = "Popup",
        onclose,
        children,
    }: {
        title?: string;
        onclose: () => void;
        children: Snippet;
    } = $props();
</script>

<div
    class="w-screen z-100 h-screen fixed top-0 left-0 flex items-center justify-center bg-black/25"
    onclick={onclose}
    role="presentation"
>
    <div
        transition:fade={{ duration: 100 }}
        class="rounded-xl p-4 bg-white flex flex-col"
        onclick={(e) => e.stopPropagation()}
        role="dialog"
        aria-modal="true"
    >
        <header class="flex flex-row justify-between mb-3">
            <h2 class="text-xl font-bold">{title}</h2>
            <button
                class="close-btn"
                onclick={onclose}
                aria-label="Close popup"
            >
                <MaterialSymbolsCloseRounded />
            </button>
        </header>

        <main>
            {@render children()}
        </main>
    </div>
</div>
