import { sveltekit } from '@sveltejs/kit/vite';
import { defineConfig } from 'vite';
import wasm from 'vite-plugin-wasm';
import topLevelAwait from 'vite-plugin-top-level-await';
import Icons from 'unplugin-icons/vite'
import tailwindcss from '@tailwindcss/vite';

export default defineConfig({
    plugins: [sveltekit(), wasm(), topLevelAwait(), Icons({ compiler: 'svelte' }), tailwindcss()],
    build: {
        target: "esnext"
    },
    worker: {
        plugins: () => [wasm(), topLevelAwait()],
        format: "es",
    }
});
