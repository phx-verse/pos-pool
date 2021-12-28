const TestServerUrl = 'http://net8888.confluxrpc.com'
const ProxyConfig = {
  target: TestServerUrl,
  changeOrigin: true,
  pathRewrite: {
    '^/rpc': '',
  },
}

module.exports = {
  style: {
    postcss: {
      plugins: [require('tailwindcss'),require('autoprefixer')],
    },
  },
  devServer: {
    historyApiFallback: true,
    proxy: {
      '/rpc': ProxyConfig,
    },
  },
  webpack: {
    configure: webpackConfig => {
      const scopePluginIndex = webpackConfig.resolve.plugins.findIndex(
        ({ constructor }) => constructor && constructor.name === 'ModuleScopePlugin'
      );

      webpackConfig.resolve.plugins.splice(scopePluginIndex, 1);
      return webpackConfig;
    }
  }
}
