package P is
   X, Y : Natural;
   procedure A (Cond : Boolean) with Subprogram_Variant => (Decreases => X, Increases => Y), Global => (Input => X);

   procedure B (A : in out Natural; Cond : Boolean) with Subprogram_Variant => (Decreases => X, Increases => Y), Global => null, Contract_Cases => (A = 0 => A = 0, others => A = A'Old);

   function C (A : Natural; Cond : Boolean) return Natural with Subprogram_Variant => (Decreases => X, Increases => Y), Global => (Input => (X, Y));
end;
