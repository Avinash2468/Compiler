(let ([x (if (> (if (>= (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                            (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                            (let ([a 2]) a))
                        (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                            (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                            (let ([a 2]) a)))
                    8
                    9)
                8)
             #t
             #f)])
  (if x
      (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
          (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
          (let ([a 2]) a))
      (let ([a (if (if (if (if (if (> (read)
                                      (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                          (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                                          (let ([a 2]) a)))
                                   (let ([a #t]) a)
                                   (let ([a #f]) a))
                               (let ([a #t]) a)
                               (let ([a #f]) a))
                           (let ([a #t]) a)
                           (let ([a #f]) a))
                       #t
                       #f)
                   (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                       (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                       (let ([a 2]) a))
                   2)])
        (+
         a
         (let ([a (if (if (if (if (> (read)
                                     (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                         (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                                         (let ([a 2]) a)))
                                  (let ([a #t]) a)
                                  (let ([a #f]) a))
                              (let ([a #t]) a)
                              (let ([a #f]) a))
                          (let ([a #t]) a)
                          (let ([a #f]) a))
                      (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                          (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                          (let ([a 2]) a))
                      2)])
           (+
            a
            (let ([a (if (if (if (if (> (read)
                                        (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                            (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                                            (let ([a 2]) a)))
                                     (let ([a #t]) a)
                                     (let ([a #f]) a))
                                 (let ([a #t]) a)
                                 (let ([a #f]) a))
                             (let ([a #t]) a)
                             (let ([a #f]) a))
                         (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                             (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                             (let ([a 2]) a))
                         2)])
              (+
               a
               (let ([a (if (if (if (if (> (read)
                                           (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                               (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))])
                                                 a)
                                               (let ([a 2]) a)))
                                        (let ([a #t]) a)
                                        (let ([a #f]) a))
                                    (let ([a #t]) a)
                                    (let ([a #f]) a))
                                (let ([a #t]) a)
                                (let ([a #f]) a))
                            (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                                (let ([a 2]) a))
                            2)])
                 (+
                  a
                  (let ([a (if (if (if (if (> (read)
                                              (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                                  (let ([a (if (> 3 1)
                                                               (let ([a 1]) a)
                                                               (let ([a 2]) a))])
                                                    a)
                                                  (let ([a 2]) a)))
                                           (let ([a #t]) a)
                                           (let ([a #f]) a))
                                       (let ([a #t]) a)
                                       (let ([a #f]) a))
                                   (let ([a #t]) a)
                                   (let ([a #f]) a))
                               (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                   (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                                   (let ([a 2]) a))
                               2)])
                    (+
                     (read)
                     (let ([a
                            (if (if (if (if (> (read)
                                               (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                                   (let ([a (if (> 3 1)
                                                                (let ([a 1]) a)
                                                                (let ([a 2]) a))])
                                                     a)
                                                   (let ([a 2]) a)))
                                            (let ([a #t]) a)
                                            (let ([a #f]) a))
                                        (let ([a #t]) a)
                                        (let ([a #f]) a))
                                    (let ([a #t]) a)
                                    (let ([a #f]) a))
                                (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                    (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                                    (let ([a 2]) a))
                                2)])
                       (+
                        a
                        (let ([a
                               (if (if (if (if (>
                                                (read)
                                                (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                                    (let ([a (if (> 3 1)
                                                                 (let ([a 1]) a)
                                                                 (let ([a 2]) a))])
                                                      a)
                                                    (let ([a 2]) a)))
                                               (let ([a #t]) a)
                                               (let ([a #f]) a))
                                           (let ([a #t]) a)
                                           (let ([a #f]) a))
                                       (let ([a #t]) a)
                                       (let ([a #f]) a))
                                   (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                       (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                                       (let ([a 2]) a))
                                   2)])
                          (+
                           a
                           (let ([a (if (if (if (if (> (read)
                                                       (if (> 3
                                                              (if (> 3 1)
                                                                  (let ([a 1]) a)
                                                                  (let ([a 2]) a)))
                                                           (let ([a (if (> 3 1)
                                                                        (let ([a 1]) a)
                                                                        (let ([a 2]) a))])
                                                             a)
                                                           (let ([a 2]) a)))
                                                    (let ([a #t]) a)
                                                    (let ([a #f]) a))
                                                (let ([a #t]) a)
                                                (let ([a #f]) a))
                                            (let ([a #t]) a)
                                            (let ([a #f]) a))
                                        (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                            (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))]) a)
                                            (let ([a 2]) a))
                                        2)])
                             (+
                              a
                              (let ([a (if (if (if (if (> (read)
                                                          (if (> 3
                                                                 (if (> 3 1)
                                                                     (let ([a 1]) a)
                                                                     (let ([a 2]) a)))
                                                              (let ([a (if (> 3 1)
                                                                           (let ([a 1]) a)
                                                                           (let ([a 2]) a))])
                                                                a)
                                                              (let ([a 2]) a)))
                                                       (let ([a #t]) a)
                                                       (let ([a #f]) a))
                                                   (let ([a #t]) a)
                                                   (let ([a #f]) a))
                                               (let ([a #t]) a)
                                               (let ([a #f]) a))
                                           (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                               (let ([a (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a))])
                                                 a)
                                               (let ([a 2]) a))
                                           2)])
                                (+
                                 a
                                 (let ([a (read)])
                                   (+
                                    a
                                    (let ([a
                                           (if (if (if (if (> (read)
                                                              (if (> 3
                                                                     (if (> 3 1)
                                                                         (let ([a 1]) a)
                                                                         (let ([a 2]) a)))
                                                                  (let ([a (if (> 3 1)
                                                                               (let ([a 1]) a)
                                                                               (let ([a 2]) a))])
                                                                    a)
                                                                  (let ([a 2]) a)))
                                                           (let ([a #t]) a)
                                                           (let ([a #f]) a))
                                                       (let ([a #t]) a)
                                                       (let ([a #f]) a))
                                                   (let ([a #t]) a)
                                                   (let ([a #f]) a))
                                               (if (> 3 (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                                   (let ([a (if (> 3 1)
                                                                (let ([a 1]) a)
                                                                (let ([a 2]) a))])
                                                     a)
                                                   (let ([a 2]) a))
                                               2)])
                                      (+
                                       a
                                       (let ([a
                                              (if (if (if (if (> (read)
                                                                 (if (> 3
                                                                        (if (> 3 1)
                                                                            (let ([a 1]) a)
                                                                            (let ([a 2]) a)))
                                                                     (let ([a (if (> 3 1)
                                                                                  (let ([a 1]) a)
                                                                                  (let ([a 2]) a))])
                                                                       a)
                                                                     (let ([a 2]) a)))
                                                              (let ([a #t]) a)
                                                              (let ([a #f]) a))
                                                          (let ([a #t]) a)
                                                          (let ([a #f]) a))
                                                      (let ([a #t]) a)
                                                      (let ([a #f]) a))
                                                  (if (> 3
                                                         (if (> 3 1) (let ([a 1]) a) (let ([a 2]) a)))
                                                      (let ([a (if (> 3 1)
                                                                   (let ([a 1]) a)
                                                                   (let ([a 2]) a))])
                                                        a)
                                                      (let ([a 2]) a))
                                                  2)])
                                         a)))))))))))))))))))))))))