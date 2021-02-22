package Recursive_Subprograms.Mutually with SPARK_Mode is
   function Is_Odd (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);
   function Is_Even (X : Natural) return Boolean with
     Subprogram_Variant => (Decreases => X);

   function Is_Odd (X : Natural) return Boolean is
     (if X = 0 then False else not Is_Even (X - 1));
   function Is_Even (X : Natural) return Boolean is
     (if X = 0 then True else not Is_Odd (X - 1));
end Recursive_Subprograms.Mutually;
