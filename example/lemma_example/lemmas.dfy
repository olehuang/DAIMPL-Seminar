lemma Sum(n: nat)
    ensures SumOfN(n) == n * (n + 1) / 2  // Conclusion: The goal of this lemma is to prove
{
    // Proof process (the core of the lemma)
    // Inductive proofs typically involve recursive calls and assertions.
    if n > 0 {
        // Recursive call, assuming the conclusion holds true at time n-1 (inductive hypothesis).
        Sum(n - 1); 
    }
}

// Helper functions for calculating the sum of numbers from 1 to n.
function SumOfN(n: nat): nat {
    if n == 0 then 0 else SumOfN(n - 1) + n
}
