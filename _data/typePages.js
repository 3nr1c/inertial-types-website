const fs = require('fs');
const path = require('path');

module.exports = function() {
    const typesDir = path.join(__dirname, 'types');
    let allTypes = [];

    // Safety check
    if (!fs.existsSync(typesDir)) return allTypes;

    const folders = fs.readdirSync(typesDir);

    folders.forEach(folder => {
        const folderPath = path.join(typesDir, folder);
        
        if (fs.statSync(folderPath).isDirectory()) {
            const files = fs.readdirSync(folderPath).filter(f => f.endsWith('.json'));
            
            files.forEach(file => {
                const rawData = fs.readFileSync(path.join(folderPath, file), 'utf8');
                const data = JSON.parse(rawData);
                
                data.id = `${path.parse(file).name}`;
                allTypes.push(data);
            });
        }
    });

    // Helper function to assign a sorting weight based on the description
    const getCategoryWeight = (description) => {
        if (!description) return 99; // Unknown types go to the bottom
        const desc = description.toLowerCase();
        
        if (desc.includes('principal')) return 1;
        if (desc.includes('unramified')) return 2; // Catches supercuspidal/supersingular unramified
        if (desc.includes('ramified')) return 3;   // Catches supercuspidal/supersingular ramified
        if (desc.includes('q8')) return 4;         // Catches "exceptional q8" or "exceptional, Q8"
        if (desc.includes('sl(2,3)')) return 5;    // Catches "exceptional sl(2,3)" or "exceptional, SL(2,3)"
        
        return 99;
    };

    // Sort the entire array
    allTypes.sort((a, b) => {
        // 1. Sort by Description Category Order
        const weightA = getCategoryWeight(a.Description);
        const weightB = getCategoryWeight(b.Description);
        
        if (weightA !== weightB) {
            return weightA - weightB;
        }

        // 2. Sort by v(N) (Ascending)
        const vA = Number(a["v(N)"]) || 0;
        const vB = Number(b["v(N)"]) || 0;
        
        if (vA !== vB) {
            return vA - vB;
        }

        // 3. Sort by Character Order (Ascending)
        const charA = Number(a["Character Order"]) || 0;
        const charB = Number(b["Character Order"]) || 0;
        
        return charA - charB;
    });

    return allTypes;
};