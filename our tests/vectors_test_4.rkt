(let ([sum 6])
(let ([i 8])
(begin
(while (> i 0)
(begin
(set! sum (+ sum i))
(set! i (- i 1))))
sum)))
