function AddConductor(chars, groups, maps, order)
    return [*[* chi, ComputeConductor(chi, groups, maps), order *] : chi in chars *];
end function;