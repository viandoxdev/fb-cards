<script lang="ts">
    import Popup from "$lib/Popup.svelte";
    import { settings, resetSettings } from "$lib/settings.svelte";

    let { onclose }: { onclose: () => void } = $props();
</script>

<Popup title="Settings" {onclose}>
    <div class="flex flex-col gap-6 w-72 sm:w-80 px-1 pb-1">
        <div class="flex flex-col gap-2">
            <div class="flex flex-row justify-between items-baseline">
                <label for="font_size" class="font-medium text-slate-800">
                    Font size
                </label>
                <span
                    class="text-sm text-slate-500 tabular-nums font-mono px-2 py-0.5 rounded bg-slate-100"
                >
                    {settings.fontSize}
                </span>
            </div>
            <input
                id="font_size"
                bind:value={settings.fontSize}
                type="range"
                min="0"
                max="40"
                class="w-full accent-indigo-500 cursor-pointer"
            />
        </div>

        <label
            class="flex flex-row items-center justify-between cursor-pointer select-none"
        >
            <span class="font-medium text-slate-800">Sans math font</span>
            <span class="relative inline-flex items-center">
                <input
                    type="checkbox"
                    class="sr-only peer"
                    bind:checked={settings.useSansFont}
                />
                <span
                    class="w-11 h-6 rounded-full bg-slate-300 peer-checked:bg-indigo-500 transition-colors"
                ></span>
                <span
                    class="absolute top-0.5 left-0.5 w-5 h-5 rounded-full bg-white shadow transition-transform peer-checked:translate-x-5"
                ></span>
            </span>
        </label>

        <button
            type="button"
            class="self-end text-sm text-slate-500 hover:text-indigo-500 transition-colors cursor-pointer"
            onclick={resetSettings}
        >
            Reset to defaults
        </button>
    </div>
</Popup>
