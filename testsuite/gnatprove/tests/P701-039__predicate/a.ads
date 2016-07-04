package A is

 subtype Pred is Integer with Static_Predicate => Pred in 1 .. 5;

 type Rec (Disc : Pred := 10) is record
    case Disc is
       when 1 .. 4 => A : Integer;
       when 5 => B : Integer;
    end case;
 end record;

 A : Rec;

end A;
