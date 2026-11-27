# Negative clock-pair inverse receipts

Four closed left-inverse equations for the exact two-donor observation
matrices. They were checked using Lean 4.36.0 and `decide +kernel`:

| Target order | Matrix size | Two clock observations |
|---:|---:|---|
|13|7|−9, −11|
|15|8|−1301, −1303|
|17|9|−1501, −1503|
|19|10|−1701, −1703|

The proofs do not assume those clocks have already been realized
as pure physical rows. They are independent of the order-thirteen
witness and do not, by themselves, prove any RK order bound at
15, 17, or 19. Regenerate with `python3 gen_mixed.py` (SymPy).
