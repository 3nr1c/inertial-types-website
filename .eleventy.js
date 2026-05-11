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
        formattedStr = formattedStr.replace(/\(([a-z\.\d\s\]\-]+)\s*\+\s*O\((\d|[a-z]|\$\.1)\^\{\d+\}\)\)/g, "$1");
        formattedStr = formattedStr.replace(/([a-z\.\d\s]+)\s*\+\s*O\((\d|[a-z]|\$\.1)\^\{\d+\}\)/g, "$1");

        // Remove parenthesis for single-summand expressions
        formattedStr = formattedStr.replace(/\(([^\)\+-]+)\)/g, "$1");
        
        return formattedStr;
    });

    eleventyConfig.addFilter("sortByDegree", function(entries) {
        return entries.sort((a, b) => {
            // 'entries' from dictsort are [key, value] pairs. We want the 'label' from the value.
            const labelA = a[1].label || "";
            const labelB = b[1].label || "";

            const getDegree = (label) => {
                const parts = label.split('.').map(Number);
                // If the label has at least 3 parts (e.g., 2.4.2.1)
                if (parts.length >= 3) {
                    return parts[1] * parts[2]; // Second number * Third number
                }
                // Fallback for labels like "Q2" that don't fit the pattern
                return 0;
            };

            return getDegree(labelA) - getDegree(labelB);
        });
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
