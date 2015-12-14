-- Package Pred
package Pred is
  type A_Type is private;
  subtype A_Subtype is A_Type with Dynamic_Predicate => True;
private
  type A_Type is null record;
end Pred;
