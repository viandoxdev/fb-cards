import adapter from '@sveltejs/adapter-static';

/** @type {import('@sveltejs/kit').Config} */
const config = { 
    kit: {
        adapter: adapter(),
        prerender: {
            handleHttpError: ({ path, message }) => {
                // Ingore 404 for generated _full.pdf file
                if (path === '/_full.pdf') {
                    console.warn(`Ignoring missing {path} during build`);
                    return;
                }

                throw new Error(message);
            }
        }
    }
};

export default config;
