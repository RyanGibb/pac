(* Yarn Berry's built-in packageExtensions, @yarnpkg/extensions 2.0.6 as
   Yarn 4.14.1 bundles it (packages/yarnpkg-extensions/sources/index.ts):
   for each package descriptor, the dependencies and peer dependencies
   Berry adds to a matching version whose manifest names none, and the
   peerDependenciesMeta it sets.  Generated from that list. *)

type t = {
  x_name : string;
  x_range : string;
  x_deps : (string * string) list;
  x_peers : (string * string) list;
  x_meta : (string * bool) list;
}

let all =
  [
    {
      x_name = "@tailwindcss/aspect-ratio";
      x_range = "<0.2.1";
      x_deps = [];
      x_peers = [ ("tailwindcss", "^2.0.2") ];
      x_meta = [];
    };
    {
      x_name = "@tailwindcss/line-clamp";
      x_range = "<0.2.1";
      x_deps = [];
      x_peers = [ ("tailwindcss", "^2.0.2") ];
      x_meta = [];
    };
    {
      x_name = "@fullhuman/postcss-purgecss";
      x_range = "3.1.3 || 3.1.3-alpha.0";
      x_deps = [];
      x_peers = [ ("postcss", "^8.0.0") ];
      x_meta = [];
    };
    {
      x_name = "@samverschueren/stream-to-observable";
      x_range = "<0.3.1";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("rxjs", true); ("zenObservable", true) ];
    };
    {
      x_name = "any-observable";
      x_range = "<0.5.1";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("rxjs", true); ("zenObservable", true) ];
    };
    {
      x_name = "@pm2/agent";
      x_range = "<1.0.4";
      x_deps = [ ("debug", "*") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "debug";
      x_range = "<4.2.0";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("supports-color", true) ];
    };
    {
      x_name = "got";
      x_range = "<11";
      x_deps = [ ("@types/responselike", "^1.0.0"); ("@types/keyv", "^3.1.1") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "cacheable-lookup";
      x_range = "<4.1.2";
      x_deps = [ ("@types/keyv", "^3.1.1") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "http-link-dataloader";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("graphql", "^0.13.1 || ^14.0.0") ];
      x_meta = [];
    };
    {
      x_name = "typescript-language-server";
      x_range = "*";
      x_deps =
        [
          ("vscode-jsonrpc", "^5.0.1");
          ("vscode-languageserver-protocol", "^3.15.0");
        ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "postcss-syntax";
      x_range = "*";
      x_deps = [];
      x_peers = [];
      x_meta =
        [
          ("postcss-html", true);
          ("postcss-jsx", true);
          ("postcss-less", true);
          ("postcss-markdown", true);
          ("postcss-scss", true);
        ];
    };
    {
      x_name = "jss-plugin-rule-value-function";
      x_range = "<=10.1.1";
      x_deps = [ ("tiny-warning", "^1.0.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "ink-select-input";
      x_range = "<4.1.0";
      x_deps = [];
      x_peers = [ ("react", "^16.8.2") ];
      x_meta = [];
    };
    {
      x_name = "license-webpack-plugin";
      x_range = "<2.3.18";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("webpack", true) ];
    };
    {
      x_name = "snowpack";
      x_range = ">=3.3.0";
      x_deps = [ ("node-gyp", "^7.1.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "promise-inflight";
      x_range = "*";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("bluebird", true) ];
    };
    {
      x_name = "reactcss";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("react", "*") ];
      x_meta = [];
    };
    {
      x_name = "react-color";
      x_range = "<=2.19.0";
      x_deps = [];
      x_peers = [ ("react", "*") ];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-i18n";
      x_range = "*";
      x_deps = [ ("ramda", "^0.24.1") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "useragent";
      x_range = "^2.0.0";
      x_deps =
        [ ("request", "^2.88.0"); ("yamlparser", "0.0.x"); ("semver", "5.5.x") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "@apollographql/apollo-tools";
      x_range = "<=0.5.2";
      x_deps = [];
      x_peers = [ ("graphql", "^14.2.1 || ^15.0.0") ];
      x_meta = [];
    };
    {
      x_name = "material-table";
      x_range = "^2.0.0";
      x_deps = [ ("@babel/runtime", "^7.11.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "@babel/parser";
      x_range = "*";
      x_deps = [ ("@babel/types", "^7.8.3") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "fork-ts-checker-webpack-plugin";
      x_range = "<=6.3.4";
      x_deps = [];
      x_peers =
        [
          ("eslint", ">= 6");
          ("typescript", ">= 2.7");
          ("webpack", ">= 4");
          ("vue-template-compiler", "*");
        ];
      x_meta = [ ("eslint", true); ("vue-template-compiler", true) ];
    };
    {
      x_name = "rc-animate";
      x_range = "<=3.1.1";
      x_deps = [];
      x_peers = [ ("react", ">=16.9.0"); ("react-dom", ">=16.9.0") ];
      x_meta = [];
    };
    {
      x_name = "react-bootstrap-table2-paginator";
      x_range = "*";
      x_deps = [ ("classnames", "^2.2.6") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "react-draggable";
      x_range = "<=4.4.3";
      x_deps = [];
      x_peers = [ ("react", ">= 16.3.0"); ("react-dom", ">= 16.3.0") ];
      x_meta = [];
    };
    {
      x_name = "apollo-upload-client";
      x_range = "<14";
      x_deps = [];
      x_peers = [ ("graphql", "14 - 15") ];
      x_meta = [];
    };
    {
      x_name = "react-instantsearch-core";
      x_range = "<=6.7.0";
      x_deps = [];
      x_peers = [ ("algoliasearch", ">= 3.1 < 5") ];
      x_meta = [];
    };
    {
      x_name = "react-instantsearch-dom";
      x_range = "<=6.7.0";
      x_deps = [ ("react-fast-compare", "^3.0.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "ws";
      x_range = "<7.2.1";
      x_deps = [];
      x_peers = [ ("bufferutil", "^4.0.1"); ("utf-8-validate", "^5.0.2") ];
      x_meta = [ ("bufferutil", true); ("utf-8-validate", true) ];
    };
    {
      x_name = "react-portal";
      x_range = "<4.2.2";
      x_deps = [];
      x_peers = [ ("react-dom", "^15.0.0-0 || ^16.0.0-0 || ^17.0.0-0") ];
      x_meta = [];
    };
    {
      x_name = "react-scripts";
      x_range = "<=4.0.1";
      x_deps = [];
      x_peers = [ ("react", "*") ];
      x_meta = [];
    };
    {
      x_name = "testcafe";
      x_range = "<=1.10.1";
      x_deps =
        [
          ("@babel/plugin-transform-for-of", "^7.12.1");
          ("@babel/runtime", "^7.12.5");
        ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "testcafe-legacy-api";
      x_range = "<=4.2.0";
      x_deps =
        [ ("testcafe-hammerhead", "^17.0.1"); ("read-file-relative", "^1.2.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "@google-cloud/firestore";
      x_range = "<=4.9.3";
      x_deps = [ ("protobufjs", "^6.8.6") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-source-apiserver";
      x_range = "*";
      x_deps = [ ("babel-polyfill", "^6.26.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "@webpack-cli/package-utils";
      x_range = "<=1.0.1-alpha.4";
      x_deps = [ ("cross-spawn", "^7.0.3") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-remark-prismjs";
      x_range = "<3.3.28";
      x_deps = [ ("lodash", "^4") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-favicon";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("webpack", "*") ];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-sharp";
      x_range = "<=4.6.0-next.3";
      x_deps = [ ("debug", "^4.3.1") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-react-router-scroll";
      x_range = "<=5.6.0-next.0";
      x_deps = [ ("prop-types", "^15.7.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "@rebass/forms";
      x_range = "*";
      x_deps = [ ("@styled-system/should-forward-prop", "^5.0.0") ];
      x_peers = [ ("react", "^16.8.6") ];
      x_meta = [];
    };
    {
      x_name = "rebass";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("react", "^16.8.6") ];
      x_meta = [];
    };
    {
      x_name = "@ant-design/react-slick";
      x_range = "<=0.28.3";
      x_deps = [];
      x_peers = [ ("react", ">=16.0.0") ];
      x_meta = [];
    };
    {
      x_name = "mqtt";
      x_range = "<4.2.7";
      x_deps = [ ("duplexify", "^4.1.1") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "vue-cli-plugin-vuetify";
      x_range = "<=2.0.3";
      x_deps = [ ("semver", "^6.3.0") ];
      x_peers = [];
      x_meta = [ ("sass-loader", true); ("vuetify-loader", true) ];
    };
    {
      x_name = "vue-cli-plugin-vuetify";
      x_range = "<=2.0.4";
      x_deps = [ ("null-loader", "^3.0.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "vue-cli-plugin-vuetify";
      x_range = ">=2.4.3";
      x_deps = [];
      x_peers = [ ("vue", "*") ];
      x_meta = [];
    };
    {
      x_name = "@vuetify/cli-plugin-utils";
      x_range = "<=0.0.4";
      x_deps = [ ("semver", "^6.3.0") ];
      x_peers = [];
      x_meta = [ ("sass-loader", true) ];
    };
    {
      x_name = "@vue/cli-plugin-typescript";
      x_range = "<=5.0.0-alpha.0";
      x_deps = [ ("babel-loader", "^8.1.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "@vue/cli-plugin-typescript";
      x_range = "<=5.0.0-beta.0";
      x_deps = [ ("@babel/core", "^7.12.16") ];
      x_peers = [ ("vue-template-compiler", "^2.0.0") ];
      x_meta = [ ("vue-template-compiler", true) ];
    };
    {
      x_name = "cordova-ios";
      x_range = "<=6.3.0";
      x_deps = [ ("underscore", "^1.9.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "cordova-lib";
      x_range = "<=10.0.1";
      x_deps = [ ("underscore", "^1.9.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "git-node-fs";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("js-git", "^0.7.8") ];
      x_meta = [ ("js-git", true) ];
    };
    {
      x_name = "consolidate";
      x_range = "<0.16.0";
      x_deps = [];
      x_peers = [ ("mustache", "^3.0.0") ];
      x_meta = [ ("mustache", true) ];
    };
    {
      x_name = "consolidate";
      x_range = "<=0.16.0";
      x_deps = [];
      x_peers =
        [
          ("velocityjs", "^2.0.1");
          ("tinyliquid", "^0.2.34");
          ("liquid-node", "^3.0.1");
          ("jade", "^1.11.0");
          ("then-jade", "*");
          ("dust", "^0.3.0");
          ("dustjs-helpers", "^1.7.4");
          ("dustjs-linkedin", "^2.7.5");
          ("swig", "^1.4.2");
          ("swig-templates", "^2.0.3");
          ("razor-tmpl", "^1.3.1");
          ("atpl", ">=0.7.6");
          ("liquor", "^0.0.5");
          ("twig", "^1.15.2");
          ("ejs", "^3.1.5");
          ("eco", "^1.1.0-rc-3");
          ("jazz", "^0.0.18");
          ("jqtpl", "~1.1.0");
          ("hamljs", "^0.6.2");
          ("hamlet", "^0.3.3");
          ("whiskers", "^0.4.0");
          ("haml-coffee", "^1.14.1");
          ("hogan.js", "^3.0.2");
          ("templayed", ">=0.2.3");
          ("handlebars", "^4.7.6");
          ("underscore", "^1.11.0");
          ("lodash", "^4.17.20");
          ("pug", "^3.0.0");
          ("then-pug", "*");
          ("qejs", "^3.0.5");
          ("walrus", "^0.10.1");
          ("mustache", "^4.0.1");
          ("just", "^0.1.8");
          ("ect", "^0.5.9");
          ("mote", "^0.2.0");
          ("toffee", "^0.3.6");
          ("dot", "^1.1.3");
          ("bracket-template", "^1.1.5");
          ("ractive", "^1.3.12");
          ("nunjucks", "^3.2.2");
          ("htmling", "^0.0.8");
          ("babel-core", "^6.26.3");
          ("plates", "~0.4.11");
          ("react-dom", "^16.13.1");
          ("react", "^16.13.1");
          ("arc-templates", "^0.5.3");
          ("vash", "^0.13.0");
          ("slm", "^2.0.0");
          ("marko", "^3.14.4");
          ("teacup", "^2.0.0");
          ("coffee-script", "^1.12.7");
          ("squirrelly", "^5.1.0");
          ("twing", "^5.0.2");
        ];
      x_meta =
        [
          ("velocityjs", true);
          ("tinyliquid", true);
          ("liquid-node", true);
          ("jade", true);
          ("then-jade", true);
          ("dust", true);
          ("dustjs-helpers", true);
          ("dustjs-linkedin", true);
          ("swig", true);
          ("swig-templates", true);
          ("razor-tmpl", true);
          ("atpl", true);
          ("liquor", true);
          ("twig", true);
          ("ejs", true);
          ("eco", true);
          ("jazz", true);
          ("jqtpl", true);
          ("hamljs", true);
          ("hamlet", true);
          ("whiskers", true);
          ("haml-coffee", true);
          ("hogan.js", true);
          ("templayed", true);
          ("handlebars", true);
          ("underscore", true);
          ("lodash", true);
          ("pug", true);
          ("then-pug", true);
          ("qejs", true);
          ("walrus", true);
          ("mustache", true);
          ("just", true);
          ("ect", true);
          ("mote", true);
          ("toffee", true);
          ("dot", true);
          ("bracket-template", true);
          ("ractive", true);
          ("nunjucks", true);
          ("htmling", true);
          ("babel-core", true);
          ("plates", true);
          ("react-dom", true);
          ("react", true);
          ("arc-templates", true);
          ("vash", true);
          ("slm", true);
          ("marko", true);
          ("teacup", true);
          ("coffee-script", true);
          ("squirrelly", true);
          ("twing", true);
        ];
    };
    {
      x_name = "vue-loader";
      x_range = "<=16.3.3";
      x_deps = [];
      x_peers =
        [ ("@vue/compiler-sfc", "^3.0.8"); ("webpack", "^4.1.0 || ^5.0.0-0") ];
      x_meta = [ ("@vue/compiler-sfc", true) ];
    };
    {
      x_name = "vue-loader";
      x_range = "^16.7.0";
      x_deps = [];
      x_peers = [ ("@vue/compiler-sfc", "^3.0.8"); ("vue", "^3.2.13") ];
      x_meta = [ ("@vue/compiler-sfc", true); ("vue", true) ];
    };
    {
      x_name = "scss-parser";
      x_range = "<=1.0.5";
      x_deps = [ ("lodash", "^4.17.21") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "query-ast";
      x_range = "<1.0.5";
      x_deps = [ ("lodash", "^4.17.21") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "redux-thunk";
      x_range = "<=2.3.0";
      x_deps = [];
      x_peers = [ ("redux", "^4.0.0") ];
      x_meta = [];
    };
    {
      x_name = "skypack";
      x_range = "<=0.3.2";
      x_deps = [ ("tar", "^6.1.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "@npmcli/metavuln-calculator";
      x_range = "<2.0.0";
      x_deps = [ ("json-parse-even-better-errors", "^2.3.1") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "bin-links";
      x_range = "<2.3.0";
      x_deps = [ ("mkdirp-infer-owner", "^1.0.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "rollup-plugin-polyfill-node";
      x_range = "<=0.8.0";
      x_deps = [];
      x_peers = [ ("rollup", "^1.20.0 || ^2.0.0") ];
      x_meta = [];
    };
    {
      x_name = "snowpack";
      x_range = "<3.8.6";
      x_deps = [ ("magic-string", "^0.25.7") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "elm-webpack-loader";
      x_range = "*";
      x_deps = [ ("temp", "^0.9.4") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "winston-transport";
      x_range = "<=4.4.0";
      x_deps = [ ("logform", "^2.2.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "jest-vue-preprocessor";
      x_range = "*";
      x_deps = [ ("@babel/core", "7.8.7"); ("@babel/template", "7.8.6") ];
      x_peers = [ ("pug", "^2.0.4") ];
      x_meta = [ ("pug", true) ];
    };
    {
      x_name = "redux-persist";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("react", ">=16") ];
      x_meta = [ ("react", true) ];
    };
    {
      x_name = "sodium";
      x_range = ">=3";
      x_deps = [ ("node-gyp", "^3.8.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "babel-plugin-graphql-tag";
      x_range = "<=3.1.0";
      x_deps = [];
      x_peers = [ ("graphql", "^14.0.0 || ^15.0.0") ];
      x_meta = [];
    };
    {
      x_name = "@playwright/test";
      x_range = "<=1.14.1";
      x_deps = [ ("jest-matcher-utils", "^26.4.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "babel-plugin-remove-graphql-queries";
      x_range = "<3.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "babel-preset-gatsby-package";
      x_range = "<1.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "create-gatsby";
      x_range = "<1.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-admin";
      x_range = "<0.24.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-cli";
      x_range = "<3.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-core-utils";
      x_range = "<2.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-design-tokens";
      x_range = "<3.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-legacy-polyfills";
      x_range = "<1.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-benchmark-reporting";
      x_range = "<1.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-graphql-config";
      x_range = "<0.23.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-image";
      x_range = "<1.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-mdx";
      x_range = "<2.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-netlify-cms";
      x_range = "<5.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-no-sourcemaps";
      x_range = "<3.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-page-creator";
      x_range = "<3.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-preact";
      x_range = "<5.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-preload-fonts";
      x_range = "<2.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-schema-snapshot";
      x_range = "<2.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-styletron";
      x_range = "<6.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-subfont";
      x_range = "<3.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-utils";
      x_range = "<1.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-recipes";
      x_range = "<0.25.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-source-shopify";
      x_range = "<5.6.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-source-wikipedia";
      x_range = "<3.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-transformer-screenshot";
      x_range = "<3.14.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-worker";
      x_range = "<0.5.0-next.1";
      x_deps = [ ("@babel/runtime", "^7.14.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-core-utils";
      x_range = "<2.14.0-next.1";
      x_deps = [ ("got", "8.3.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-gatsby-cloud";
      x_range = "<=3.1.0-next.0";
      x_deps = [ ("gatsby-core-utils", "^2.13.0-next.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-gatsby-cloud";
      x_range = "<=3.2.0-next.1";
      x_deps = [];
      x_peers = [ ("webpack", "*") ];
      x_meta = [];
    };
    {
      x_name = "babel-plugin-remove-graphql-queries";
      x_range = "<=3.14.0-next.1";
      x_deps = [ ("gatsby-core-utils", "^2.8.0-next.1") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-netlify";
      x_range = "3.13.0-next.1";
      x_deps = [ ("gatsby-core-utils", "^2.13.0-next.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "clipanion-v3-codemod";
      x_range = "<=0.2.0";
      x_deps = [];
      x_peers = [ ("jscodeshift", "^0.11.0") ];
      x_meta = [];
    };
    {
      x_name = "react-live";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("react-dom", "*"); ("react", "*") ];
      x_meta = [];
    };
    {
      x_name = "webpack";
      x_range = "<4.44.1";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("webpack-cli", true); ("webpack-command", true) ];
    };
    {
      x_name = "webpack";
      x_range = "<5.0.0-beta.23";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("webpack-cli", true) ];
    };
    {
      x_name = "webpack-dev-server";
      x_range = "<3.10.2";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("webpack-cli", true) ];
    };
    {
      x_name = "@docusaurus/responsive-loader";
      x_range = "<1.5.0";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("sharp", true); ("jimp", true) ];
    };
    {
      x_name = "eslint-module-utils";
      x_range = "*";
      x_deps = [];
      x_peers = [];
      x_meta =
        [
          ("eslint-import-resolver-node", true);
          ("eslint-import-resolver-typescript", true);
          ("eslint-import-resolver-webpack", true);
          ("@typescript-eslint/parser", true);
        ];
    };
    {
      x_name = "eslint-plugin-import";
      x_range = "*";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("@typescript-eslint/parser", true) ];
    };
    {
      x_name = "critters-webpack-plugin";
      x_range = "<3.0.2";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("html-webpack-plugin", true) ];
    };
    {
      x_name = "terser";
      x_range = "<=5.10.0";
      x_deps = [ ("acorn", "^8.5.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "babel-preset-react-app";
      x_range = "10.0.x <10.0.2";
      x_deps =
        [ ("@babel/plugin-proposal-private-property-in-object", "^7.16.7") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "eslint-config-react-app";
      x_range = "*";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("typescript", true) ];
    };
    {
      x_name = "@vue/eslint-config-typescript";
      x_range = "<11.0.0";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("typescript", true) ];
    };
    {
      x_name = "unplugin-vue2-script-setup";
      x_range = "<0.9.1";
      x_deps = [];
      x_peers =
        [ ("@vue/composition-api", "^1.4.3"); ("@vue/runtime-dom", "^3.2.26") ];
      x_meta = [];
    };
    {
      x_name = "@cypress/snapshot";
      x_range = "*";
      x_deps = [ ("debug", "^3.2.7") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "auto-relay";
      x_range = "<=0.14.0";
      x_deps = [];
      x_peers = [ ("reflect-metadata", "^0.1.13") ];
      x_meta = [];
    };
    {
      x_name = "vue-template-babel-compiler";
      x_range = "<1.2.0";
      x_deps = [];
      x_peers = [ ("vue-template-compiler", "^2.6.0") ];
      x_meta = [];
    };
    {
      x_name = "@parcel/transformer-image";
      x_range = "<2.5.0";
      x_deps = [];
      x_peers = [ ("@parcel/core", "*") ];
      x_meta = [];
    };
    {
      x_name = "@parcel/transformer-js";
      x_range = "<2.5.0";
      x_deps = [];
      x_peers = [ ("@parcel/core", "*") ];
      x_meta = [];
    };
    {
      x_name = "parcel";
      x_range = "*";
      x_deps = [];
      x_peers = [];
      x_meta = [ ("@parcel/core", true) ];
    };
    {
      x_name = "react-scripts";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("eslint", "*") ];
      x_meta = [];
    };
    {
      x_name = "focus-trap-react";
      x_range = "^8.0.0";
      x_deps = [ ("tabbable", "^5.3.2") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "react-rnd";
      x_range = "<10.3.7";
      x_deps = [];
      x_peers = [ ("react", ">=16.3.0"); ("react-dom", ">=16.3.0") ];
      x_meta = [];
    };
    {
      x_name = "connect-mongo";
      x_range = "<5.0.0";
      x_deps = [];
      x_peers = [ ("express-session", "^1.17.1") ];
      x_meta = [];
    };
    {
      x_name = "vue-i18n";
      x_range = "<9";
      x_deps = [];
      x_peers = [ ("vue", "^2") ];
      x_meta = [];
    };
    {
      x_name = "vue-router";
      x_range = "<4";
      x_deps = [];
      x_peers = [ ("vue", "^2") ];
      x_meta = [];
    };
    {
      x_name = "unified";
      x_range = "<10";
      x_deps = [ ("@types/unist", "^2.0.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "react-github-btn";
      x_range = "<=1.3.0";
      x_deps = [];
      x_peers = [ ("react", ">=16.3.0") ];
      x_meta = [];
    };
    {
      x_name = "react-dev-utils";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("typescript", ">=2.7"); ("webpack", ">=4") ];
      x_meta = [ ("typescript", true) ];
    };
    {
      x_name = "@asyncapi/react-component";
      x_range = "<=1.0.0-next.39";
      x_deps = [];
      x_peers = [ ("react", ">=16.8.0"); ("react-dom", ">=16.8.0") ];
      x_meta = [];
    };
    {
      x_name = "xo";
      x_range = "*";
      x_deps = [];
      x_peers = [ ("webpack", ">=1.11.0") ];
      x_meta = [ ("webpack", true) ];
    };
    {
      x_name = "babel-plugin-remove-graphql-queries";
      x_range = "<=4.20.0-next.0";
      x_deps = [ ("@babel/types", "^7.15.4") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-page-creator";
      x_range = "<=4.20.0-next.1";
      x_deps = [ ("fs-extra", "^10.1.0") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-utils";
      x_range = "<=3.14.0-next.1";
      x_deps = [ ("fastq", "^1.13.0") ];
      x_peers = [ ("graphql", "^15.0.0") ];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-mdx";
      x_range = "<3.1.0-next.1";
      x_deps = [ ("mkdirp", "^1.0.4") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "gatsby-plugin-mdx";
      x_range = "^2";
      x_deps = [];
      x_peers = [ ("gatsby", "^3.0.0-next") ];
      x_meta = [];
    };
    {
      x_name = "fdir";
      x_range = "<=5.2.0";
      x_deps = [];
      x_peers = [ ("picomatch", "2.x") ];
      x_meta = [ ("picomatch", true) ];
    };
    {
      x_name = "babel-plugin-transform-typescript-metadata";
      x_range = "<=0.3.2";
      x_deps = [];
      x_peers = [ ("@babel/core", "^7"); ("@babel/traverse", "^7") ];
      x_meta = [ ("@babel/traverse", true) ];
    };
    {
      x_name = "graphql-compose";
      x_range = ">=9.0.10";
      x_deps = [];
      x_peers = [ ("graphql", "^14.2.0 || ^15.0.0 || ^16.0.0") ];
      x_meta = [];
    };
    {
      x_name = "vite-plugin-vuetify";
      x_range = "<=1.0.2";
      x_deps = [];
      x_peers = [ ("vue", "^3.0.0") ];
      x_meta = [];
    };
    {
      x_name = "webpack-plugin-vuetify";
      x_range = "<=2.0.1";
      x_deps = [];
      x_peers = [ ("vue", "^3.2.6") ];
      x_meta = [];
    };
    {
      x_name = "eslint-import-resolver-vite";
      x_range = "<2.0.1";
      x_deps = [ ("debug", "^4.3.4"); ("resolve", "^1.22.8") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "notistack";
      x_range = "^3.0.0";
      x_deps = [ ("csstype", "^3.0.10") ];
      x_peers = [];
      x_meta = [];
    };
    {
      x_name = "@fastify/type-provider-typebox";
      x_range = "^5.0.0";
      x_deps = [];
      x_peers = [ ("fastify", "^5.0.0") ];
      x_meta = [];
    };
    {
      x_name = "@fastify/type-provider-typebox";
      x_range = "^4.0.0";
      x_deps = [];
      x_peers = [ ("fastify", "^4.0.0") ];
      x_meta = [];
    };
  ]
