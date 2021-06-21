with Element_Lists; use Element_Lists; use Element_Lists.Lists;
with Ada.Containers; use Ada.Containers; use Element_Lists.Lists.Formal_Model;

function My_Find (L : List; E : Element_Type) return Cursor with
  SPARK_Mode,
  Contract_Cases =>
    (Contains (L, E)     => Has_Element (L, My_Find'Result) and then
                            Element (L, My_Find'Result) = E,
     not Contains (L, E) => My_Find'Result = No_Element);
