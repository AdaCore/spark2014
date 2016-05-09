generic
package Bits_Manipulation.Functions with SPARK_Mode is

   function Shift_Right (V : Modular; Amount : Natural) return Modular
     with Inline_Always;

   function Shift_Left (V : Modular; Amount : Natural) return Modular
     with Inline_Always;

   function Make_Mask (Num_Bits : Mask_Size) return Modular
     with Inline_Always;

   function Extract_Bits (Value : Modular; From, To : Bit_Position) return Modular
     with
       Inline_Always,
       Pre    => (To >= From),
       Post   => ((Extract_Bits'Result =
                  (Shift_Right (Value, From) and Make_Mask (Mask_Size (To - From + 1))))
                  and then (Extract_Bits'Result <= Make_Mask (Mask_Size (To - From + 1)))
                  and then (Shift_Left (Extract_Bits'Result, From) =
                    (Value and Shift_Left(Make_Mask (Mask_Size (To - From + 1)), From))));

   function MSB_Index (Value : Modular) return Bit_Position
     with
       Inline_Always,
       Pre => Value /= 0,
       Post => Shift_Right (Value , MSB_Index'Result) = 1;

   package Lemmas with Ghost is

      package Shift_Right is

         package Assertions is

            function Lemma1 return Boolean is
              (for all Val in Modular =>
                 (for all n in Bit_Position =>
                      (Modular (2) ** n) /= 0 and then
                  Functions.Shift_Right (Val, n) = Val / (2 ** n)));
            --
            -- ∀ Val∈ Modular,N∈ Bit_Position⟹ Shift_Right〔Val, N〕≡ Val/2ⁿ
            --

            function Lemma2 return Boolean is
              (for all Val in Modular =>
                  Functions.Shift_Right (Val, 0) = Val);
            --
            -- ∀ Val∈ Modular⟹Shift_Right〔Val, 0〕≡ Val
            --

            function Lemma3 return Boolean is
              (for all Val in Modular =>
                 (if Val /= 0 then
                      (for all N in Bit_Position =>
                           (if (for all j in 0 .. N =>
                                       Functions.Shift_Right (Val, j) >= 1) and then
                              (for all j in N .. Bit_Position'Last =>
                                      Functions.Shift_Right (Val, j) <= 1) then
                                 Functions.Shift_Right (Val, N) = 1))));
            --
            -- ∀ Val∈Modular⟹
            --  〔Val≠0⟹
            --    〔∀N∈Bit_Position⟹
            --    〔〔∀j∈0…N⟹Shift_Right〔Val, N〕≥1〕∧
            --      〔∀j∈N…Bit_Position'Last⟹Shift_Right〔Val, N〕≤1〕⟹
            --          Shift_Right〔Val, N〕= 1〕〕〕
            --

            function Lemma4 return Boolean is
              (for all Val in Modular =>
                 (for all N in 1 .. Bit_Position'Last =>
                      (Functions.Shift_Right (Val, N - 1) >=
                             Functions.Shift_Right (Val, N))));
            --
            -- ∀ Val∈Modular,N∈1…Bit_Position'Last⟹
            --     Shift_Right〔Val, N - 1〕≥Shift_Right〔Val, N〕
            --

            function Lemma5 return Boolean is
              (for all Val in Modular =>
                 (for all N in 1 .. Bit_Position'Last =>
                      (if (Functions.Shift_Right (Val, N - 1) > 0 or
                               Functions.Shift_Right (Val, N) > 0)
                       then
                         (Functions.Shift_Right (Val, N - 1) >
                              Functions.Shift_Right (Val, N)))));
            --
            -- ∀ Val∈Modular,N∈1…Bit_Position'Last⟹
            --     〔〔Shift_Right〔Val, N-1〕>0 ∨ Shift_Right〔Val, N〕>0〕⟹
            --          Shift_Right〔Val, N - 1〕 > Shift_Right〔Val, N〕〕
            --

            function Lemma6 return Boolean is
              (for all Val in Modular =>
                 (if Val /= 0 then
                      (Functions.Shift_Right (Val, 0) = Val
                       and
                         (for some N in Bit_Position =>
                            (Functions.Shift_Right (Val, N) = 1
                             and then
                               (for all j in  0 .. N =>
                                     Functions.Shift_Right (Val, j) >= 1)
                             and then
                               (for all j in N .. Bit_Position'Last =>
                                     Functions.Shift_Right (Val, j) <= 1))))));
            --
            -- ∀ Val∈Modular⟹
            --  〔Val≠0⟹
            --    〔Shift_Right〔Val, 0〕≡Val∧
            --      〔∃N∈Bit_Position⟹
            --        〔〔∀j∈0…N⟹Shift_Right〔Val, j〕≥1〕∧
            --        〔∀j∈N…Bit_Position'Last⟹Shift_Right〔Val, j〕≤1〕〕〕〕〕
            --

            function Lemma7 return Boolean is
              (for all Value in Modular =>
                 (for all N in Bit_Position =>
                      (Functions.Shift_Left
                           (Functions.Shift_Right (Value, N),
                            N)) = (Value and
                                       (Functions.Shift_Left
                                        (Functions.Make_Mask (Mask_Size (Bit_Position'Last - N) + 1),
                                         N)))));
            --
            -- ∀ Val∈Modular,N∈Bit_Bosition⟹
            --  Shift_Left〔Shift_Right〔Val,N〕,N〕≡
            --  〔Value∧Shift_Left〔
            --    Make_Mask〔Bit_Position'Last-N+1〕,N〕〕
            --

            function Lemma8 return Boolean is
              (for all Val in Modular =>
                 (for all n in  Mask_Size'First .. Mask_Size'Last - 1 =>
                       Functions.Shift_Right (Val, Modular_Size - n) < Modular (2) ** n));
            --
            -- ∀ Val∈ Modular,n∈ 1…Bit_Position'Last
            --  ⟹ Shift_Right〔Val, Modular_Size - n〕< 2ⁿ
            --

         end Assertions;

         function Lemma1 return Boolean
           with Import,
           Post => (if Lemma1'Result then Assertions.Lemma1);
         --
         -- ∀ Val∈ Modular,N∈ Bit_Position⟹ Shift_Right〔Val, N〕≡ Val/2ⁿ
         --

         function Lemma2 return Boolean
           with Import,
           Post => (if Lemma2'Result then Assertions.Lemma1);
         --
         -- ∀ Val∈ Modular⟹Shift_Right〔Val, 0〕≡ Val
         --

         function Lemma3 return Boolean
           with Import,
           Post => (if Lemma3'Result then Assertions.Lemma3);
         --
         -- For fixed non-zero Value if there exists
         -- sequence of 0..N that Shift_Rigth >= 1 and
         -- sequence of N..Bit_Position'Last <= 1 then
         -- Shift_Right in N is 1.
         --
         -- This lemma is useful with lemma of strictly
         -- monotone Shift_Right as function of N
         -- for fixed non-zero Value. From these two
         -- lemmas it may be proved existence of only one
         -- N that Shift_Right in N is 1.
         --
         -- ∀ Val∈Modular⟹
         --  〔Val≠0⟹
         --    〔∀N∈Bit_Position⟹
         --    〔〔∀j∈0…N⟹Shift_Right〔Val, N〕≥1〕∧
         --      〔∀j∈N…Bit_Position'Last⟹Shift_Right〔Val, N〕≤1〕⟹
         --          Shift_Right〔Val, N〕= 1〕〕〕
         --

         function Lemma4 return Boolean
           with Import,
           Post => (if Lemma4'Result then Assertions.Lemma4);
         --
         -- Shift_Right for fixed Value as function of N
         -- is monotone decreasing function.
         --
         -- ∀ Val∈Modular,N∈1…Bit_Position'Last⟹
         --     Shift_Right〔Val, N - 1〕≥Shift_Right〔Val, N〕
         --

         function Lemma5 return Boolean
           with Import,
           Post => (if Lemma5'Result then Assertions.Lemma5);
         --
         -- Shift_Right for fixed Value as function of N
         -- is strictly monotone decreasing function.
         --
         -- ∀ Val∈Modular,N∈1…Bit_Position'Last⟹
         --     〔〔Shift_Right〔Val, N-1〕>0 ∨ Shift_Right〔Val, N〕>0〕⟹
         --          Shift_Right〔Val, N - 1〕 > Shift_Right〔Val, N〕〕
         --

         function Lemma6 return Boolean
           with Import,
           Post => (if Lemma6'Result then Assertions.Lemma6);
         --
         -- Special complex lemma for MSB_Index.
         --
         -- ∀ Val∈Modular⟹
         --  〔Val≠0⟹
         --    〔Shift_Right〔Val, 0〕≡Val∧
         --      〔∃N∈Bit_Position⟹
         --        〔〔∀j∈0…N⟹Shift_Right〔Val, j〕≥1〕∧
         --        〔∀j∈N…Bit_Position'Last⟹Shift_Right〔Val, j〕≤1〕〕〕〕〕
         --

         function Lemma7 return Boolean
           with Import,
           Post => (if Lemma7'Result then Assertions.Lemma7);
         --
         -- Right shift followed by left shift
         -- is the same as masking all bits but
         -- lowest N of them.
         --
         -- ∀ Val∈Modular,N∈Bit_Bosition⟹
         --  Shift_Left〔Shift_Right〔Val,N〕,N〕≡
         --  〔Value∧Shift_Left〔
         --    Make_Mask〔Bit_Position'Last-N+1〕,N〕〕
         --

         function Lemma8 return Boolean
           with Import,
           Post => (if Lemma8'Result then Assertions.Lemma8);
         --
         -- ∀ Val∈ Modular,n∈ 1…Bit_Position'Last
         --  ⟹ Shift_Right〔Val, Modular_Size - n〕< 2ⁿ
         --

      end Shift_Right;

      package Shift_Left is

         package Assertions is
            function Lemma1 return Boolean is
              (for all V in Modular =>
                 (for all N in Bit_Position =>
                       Functions.Shift_Left (V, N) = Modular'Mod (V * (2 ** N))));
            --
            -- ∀ Val∈Modular,n∈Bit_Bosition⟹
            --    Shift_Left〔Val, n〕≡Val×2ⁿ (mod Modular)
            --

         end Assertions;

         function Lemma1 return Boolean
           with Import,
           Post => (if Lemma1'Result then Assertions.Lemma1);
         --
         -- ∀ Val∈Modular,n∈Bit_Bosition⟹
         --    Shift_Left〔Val, n〕≡Val×2ⁿ (mod Modular)
         --

      end Shift_Left;

      package MSB_Index is
      end MSB_Index;

      package Extract_Bits is
      end Extract_Bits;

      package Make_Mask is

         package Assertions is

            function Lemma1 return Boolean is
              (for all Size in Mask_Size'First .. Mask_Size'Last - 1 =>
                  Functions.Make_Mask (Size) < Modular (2) ** (Size));

            function Lemma2 return Boolean is
              (for all Size in Mask_Size'First .. Mask_Size'Last - 1 =>
                  Functions.Make_Mask (Size) = Modular (2) ** (Size) - 1);

         end Assertions;

         function Lemma1 return Boolean
           with Import,
           Post => (if Lemma1'Result then Assertions.Lemma1);

         function Lemma2 return Boolean
           with Import,
           Post => (if Lemma2'Result then Assertions.Lemma2);

      end Make_Mask;

   end Lemmas;

   package Proofs with Ghost is
      package Make_Mask is

         function Lemma1 return Boolean
           with Post => (if Lemma1'Result then Lemmas.Make_Mask.Assertions.Lemma1);

         function Lemma2 return Boolean
           with Post => (if lemma2'Result then Lemmas.Make_Mask.Assertions.Lemma2);

      end Make_Mask;
   end Proofs;

end Bits_Manipulation.Functions;
