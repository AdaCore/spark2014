with Assign_Arr; use Assign_Arr;
procedure Ident_Arr (X : out Arr) with
  Post => (for all J in X'Range => X (J) = J);
