<script lang="ts">
    import MaterialSymbolsNoteStackOutline from "~icons/material-symbols/note-stack-outline";
    import MaterialSymbolsCloseRounded from "~icons/material-symbols/close-rounded";

    let {
        cardName,
        frontSvg,
        backSvg,
        onclose,
    }: {
        cardName: string;
        frontSvg: string;
        backSvg: string;
        onclose: () => void;
    } = $props();
</script>

<div
    class="w-full min-h-1 grow-5 bg-slate-200 flex flex-col overflow-scroll"
>
    <div class="flex flex-col p-3 m-3 rounded-xl bg-white">
        <div class="flex flex-row gap-4 items-center p-2">
            <MaterialSymbolsNoteStackOutline class="min-w-6 min-h-6" />
            <span class="grow-1 text-xl font-bold text-left">{cardName}</span>
            <button onclick={onclose} aria-label="Close card">
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
    <!-- Spacer quickfix because cards were getting cropped on mobile android -->
    <div class="w-full min-h-48"></div>
</div>
