module.exports = function(eleventyConfig) {
    
    // Add the math formatter filter
    eleventyConfig.addFilter("formatMath", function(str) {
        if (!str) return "";
        
        let formattedStr = str.replace(/\*/g, '\\cdot ');//format * as ·

        // Remove \cdot between number and variable
        formattedStr = formattedStr.replace(/([0-9\)]+)\\cdot ([^0-9]+)/g, "$1$2");
        
        // Remove monomials with coefficient O(a^b)
        formattedStr = formattedStr.replace(/\s*[\+-]\s*O\([^\)]+\)(\\cdot )?x(\^[0-9]+)?/g, "");

        // wrap exponents in curly braces { }
        formattedStr = formattedStr.replace(/\^([0-9]+)/g, '^{$1}');

        // Remove big-oh from monomial coefficients
        formattedStr = formattedStr.replace(/\(([a-z\.\d\s\]\-]+)\s*\+\s*O\([\da-z]\^\{\d+\}\)\)/g, "$1");
        formattedStr = formattedStr.replace(/([a-z\.\d\s]+)\s*\+\s*O\([\da-z]\^\{\d+\}\)/g, "$1");

        // Remove parenthesis for single-summand expressions
        formattedStr = formattedStr.replace(/\(([^\)\+-]+)\)/g, "$1");
        
        return formattedStr;
    });

    return {
        dir: {
            input: ".",
            includes: "_includes",
            data: "_data",
            output: "_site"
        }
    };
};
