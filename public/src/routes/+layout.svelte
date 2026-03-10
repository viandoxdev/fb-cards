<script lang="ts">
	import favicon from '$lib/assets/favicon.svg';
        import '@fontsource/lexend';
        import "../app.css"

	let { children } = $props();
</script>

<svelte:head>
	<link rel="icon" href={favicon} />
</svelte:head>

<style>
    @reference "../app.css";

    :global(*) {
        font-family: "Lexend", sans-serif;
    }

    :global(body) {
        @apply flex w-screen h-screen flex-col overflow-hidden;
    }
</style> 

{@render children()}
