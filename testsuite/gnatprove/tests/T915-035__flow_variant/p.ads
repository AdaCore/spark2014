package P is
   X : Natural;
   procedure A (Cond : Boolean) with Subprogram_Variant => (Decreases => X), Global => null;
end;
