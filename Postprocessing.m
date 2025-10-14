function AddConductor(chars, groups, maps)
    return [*[* chi, ComputeConductor(chi, groups, maps)*] : chi in chars *];
end function;