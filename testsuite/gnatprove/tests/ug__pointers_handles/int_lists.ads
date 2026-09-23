with List_Pointers; use List_Pointers;

package Int_Lists with SPARK_Mode is
   use Lists, Ops;

   subtype List is Pointer;

   function Valid_List (L : List) return Boolean
   is (L = Null_Pointer
       or else
         (Valid_Handle (Constant_Reference (L).Next)
          and then Valid_List (Of_Handle (Constant_Reference (L).Next))))
   with
     Ghost              => Static,
     Global             => null,
     Subprogram_Variant => (Decreases => Variant.Weight (L));

   function Cons (V : Integer; L : List) return List
   is (Create_Cell ((Value => V, Next => To_Handle (L))))
   with
     Global => null,
     Pre    => (Static => Valid_List (L)),
     Post   => (Static => Valid_List (Cons'Result));

   function Contains (L : List; V : Integer) return Boolean
   is (L /= Null_Pointer
       and then
         (Constant_Reference (L).Value = V
          or else Contains (Of_Handle (Constant_Reference (L).Next), V)))
   with
     Global             => null,
     Pre                => (Static => Valid_List (L)),
     Subprogram_Variant => (Static => (Decreases => Variant.Weight (L)));

end Int_Lists;
