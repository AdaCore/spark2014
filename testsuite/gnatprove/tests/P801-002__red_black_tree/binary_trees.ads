with Tree_Model; use Tree_Model;
use Tree_Model.D_Seq;
with Conts; use Conts;

--  This packages provides a SPARK implementation of binary trees. Since
--  SPARK forbids the use of pointers, trees are modeled using indexes inside
--  an array. The array is not global, as it would require refering to a
--  global structure in the trees type invariant which is not allowed in
--  SPARK. To avoid multiple copies, related trees are stored together forming
--  a forest.

package Binary_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Forest is private with Default_Initial_Condition => Size (Forest) = 0;
   --  Memory region shaped as a set of related binary trees

   function Size (F : Forest) return Extended_Index_Type;
   --  Number of allocated nodes in the forest

   function Valid_Root (F : Forest; I : Index_Type) return Boolean with
     Post => (if I > Size (F) then not Valid_Root'Result);
   --  Return True if I is a root of a binary tree in F

   function Parent (F : Forest; I : Index_Type) return Extended_Index_Type with
     Post => (if Valid_Root (F, I) then Parent'Result = 0)
     and then (if Size (F) = 0 then Parent'Result = 0);
   --  Parent in the corresponding binary tree

   function Position (F : Forest; I : Index_Type) return Direction with
     Pre  => Parent (F, I) /= 0;
   --  Position (Left or Right) in the corresponding binary tree

   function Peek (F : Forest; I : Index_Type; D : Direction) return Extended_Index_Type with
     Post => (if Peek'Result /= 0 then
                Position (F, Peek'Result) = D
              and then Parent (F, Peek'Result) = I
              else
                (for all J in Index_Type =>
                     (if Parent (F, J) = I then Position (F, J) /= D)))
     and (for all J in Index_Type =>
            (if Parent (F, J) = I and then Position (F, J) = D
             then Peek'Result = J));
   --  Left or right child in the corresponding binary tree

   function Model (F : Forest; Root : Index_Type) return Model_Type with
   --  The model of a tree in the forest is an array representing the path
   --  leading to each node in the binary tree if any. We could have made a
   --  function returning each path separately, but this function would have
   --  been recursive, leading to unproved VC when it is called in annotations
   --  (that is, nearly always).

     Ghost,
     Pre  => Valid_Root (F, Root),
     Post => Model'Result (Root).K
     and then Length (Model'Result (Root).A) = 0
     and then
       (for all I in Index_Type =>
          (if I /= Root then
               (if Parent (F, I) /= 0
                and then Model'Result (Parent (F, I)).K
                then Model'Result (I).K
                else not Model'Result (I).K)))
     and then
       (for all I in Index_Type =>
          (if Model'Result (I).K and then I /= Root then
               Is_Add (Model'Result (Parent (F, I)).A,
                       Position (F, I),
                       Model'Result (I).A)
          else Length (Model'Result (I).A) = 0))
     and then
       (for all I in Index_Type =>
          (if Model'Result (I).K then
               (for all J in Index_Type =>
                    (if Model'Result (J).K
                     and then Model'Result (I).A = Model'Result (J).A
                     then J = I))));

   procedure Prove_Model_Total (F : Forest; Root, I : Index_Type; D : Direction) with Ghost,
   --  Ghost function performing an induction to show that, if Peek returns 0
   --  on I and D, then every path in the forest from Root through I cannot
   --  be in direction D.

     Pre  => Valid_Root (F, Root) and then Model (F, Root) (I).K
     and then Peek (F, I, D) = 0,
     Post =>
       (for all J in Index_Type =>
          (if Model (F, Root) (J).K
           and then (Model (F, Root) (I).A < Model (F, Root) (J).A)
             then Get (Model (F, Root) (J).A, Length (Model (F, Root) (I).A) + 1) /= D));

   procedure Prove_Model_Distinct (F : Forest; T1, T2 : Index_Type) with Ghost,
   --  Ghost function performing an induction to show that trees rooted at
   --  differeny indexes in the forest are disjoint.

     Pre  => T1 /= T2 and then Valid_Root (F, T1) and then Valid_Root (F, T2),
     Post =>
       (for all I in Index_Type =>
          (not Model (F, T1) (I).K or not Model (F, T2) (I).K));

   procedure Extract (F       : in out Forest;
                      Root, I : Index_Type;
                      D       : Direction;
                      V       : out Extended_Index_Type)
     --  Extract the subtree starting at position D after I in the tree rooted
     --  at root in a separate tree. Store its root into V.

   with
     Pre  => Valid_Root (F, Root) and then Model (F, Root) (I).K,
     Post => Size (F) = Size (F)'Old
     and then Valid_Root (F, Root)
     and then V = Peek (F, I, D)'Old
     and then Peek (F, I, D) = 0
     and then (for all J in Index_Type =>
                 (if J /= V
                  then Parent (F, J) = Parent (F'Old, J)))
     and then (for all J in Index_Type =>
                 (if J /= V and Parent (F, J) /= 0
                  then Position (F, J) = Position (F'Old, J)))
     and then (for all J in Index_Type =>
                 (for all E in Direction =>
                      (if J /= I or else E /= D
                           then Peek (F, J, E) = Peek (F'Old, J, E))))
     and then
       (for all T in Index_Type =>
          (if Valid_Root (F'Old, T) and then I /= T and then V /= T then
           Valid_Root (F, T)))
     and then
       (for all T in Index_Type =>
          (if Valid_Root (F'Old, T) and then Root /= T and then V /= T then
               Model (F, T) = Model (F'Old, T)))
     and then (if V /= 0 then Valid_Root (F, V))
     and then
       (for all I in Index_Type =>
          (if Model (F, Root)'Old (I).K then
               (if V /= 0
                and then Model (F, Root)'Old (V).A <= Model (F, Root)'Old (I).A
                then Model (F, V) (I).K
                else Model (F, Root) (I).K)))
     and then
       (for all I in Index_Type =>
          (if Model (F, Root) (I).K then Model (F, Root)'Old (I).K))
     and then
       (for all I in Index_Type =>
          (if V /= 0 and then Model (F, V) (I).K then Model (F, Root)'Old (I).K))
     and then
       (for all I in Index_Type =>
          (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F, Root)'Old (I).A))
     and then
       (for all I in Index_Type =>
          (if V /= 0 and then Model (F, V) (I).K then
               Is_Concat (Model (F, Root)'Old (V).A, Model (F, V) (I).A, Model (F, Root)'Old (I).A)));

   procedure Plug (F       : in out Forest;
                   Root, I : Index_Type;
                   D       : Direction;
                   V       : Extended_Index_Type)
     --  Plug the tree rooted at V in F into the tree rooted at Root as a
     --  subtree starting at position D after I.

   with
     Pre =>  Valid_Root (F, Root) and then Model (F, Root) (I).K
     and then Peek (F, I, D) = 0 and then Root /= V
     and then (if V /= 0 then Valid_Root (F, V)),
     Post => Size (F) = Size (F'Old)
     and then V = Peek (F, I, D)
     and then
       (for all J in Index_Type =>
          (if Valid_Root (F'Old, J) and then J /= V then Valid_Root (F, J)))
     and then
       (for all J in Index_Type =>
          (if Valid_Root (F, J) then Valid_Root (F'Old, J)))
     and then (for all J in Index_Type =>
                 (if J /= V
                  then Parent (F, J) = Parent (F'Old, J)))
     and then (for all J in Index_Type =>
                 (if J /= V and Parent (F, J) /= 0
                  then Position (F, J) = Position (F'Old, J)))
     and then (for all J in Index_Type =>
                 (for all E in Direction =>
                      (if J /= I or else E /= D
                       then Peek (F, J, E) = Peek (F'Old, J, E))))
     and then
       (for all J in Index_Type =>
          (if Model (F, Root)'Old (J).K then Model (F, Root) (J).K))
     and then
       (for all J in Index_Type =>
          (if V /= 0 and then Model (F'Old, V) (J).K
           then Model (F, Root) (J).K))
     and then
       (for all I in Index_Type =>
          (if Model (F, Root) (I).K then
               (if V /= 0 and then Model (F, Root) (V).A <= Model (F, Root) (I).A
                then Model (F'Old, V) (I).K
                else Model (F'Old, Root) (I).K)))
     and then
       (for all J in Index_Type =>
                 (if Model (F, Root)'Old (J).K then Model (F, Root) (J).A = Model (F, Root)'Old (J).A))
     and then
       (for all J in Index_Type =>
                 (if V /= 0 and then Model (F'Old, V) (J).K
                  then Is_Concat (Model (F, Root) (Peek (F, I, D)).A, Model (F'Old, V) (J).A, Model (F, Root) (J).A)))
     and then
       (for all T in Index_Type =>
          (if Valid_Root (F'Old, T) and then Root /= T and then V /= T then
               Model (F, T) = Model (F'Old, T)));

   procedure Insert (F : in out Forest; Root, I : Index_Type; D : Direction; V : out Index_Type)
     --  Insert a new node in F into the tree rooted at Root at position D
     --  after I.

   with
     Pre =>  Valid_Root (F, Root) and then Model (F, Root) (I).K
     and then Peek (F, I, D) = 0 and then Size (F) < Max,
     Post => Size (F) = Size (F)'Old + 1 and then Model (F, Root) (I).K
     and then Peek (F, I, D) = V
     and then (for all I in Index_Type =>
                 (if Valid_Root (F'Old, I) then Valid_Root (F, I)
                  else not Valid_Root (F, I)))
     and then Model (F, Root) (V).K
     and then not Model (F, Root)'Old (V).K
     and then (for all J in Index_Type =>
                 (if J /= V
                  then Parent (F, J) = Parent (F'Old, J)))
     and then (for all J in Index_Type =>
                 (if J /= V and Parent (F'Old, J) /= 0
                  then Position (F, J) = Position (F'Old, J)))
     and then
       (for all J in Index_Type =>
          (if Model (F, Root) (J).K then
               Model (F, Root)'Old (J).K or J = V))
     and then
       (for all J in Index_Type =>
        (if Model (F, Root)'Old (J).K then Model (F, Root) (J).K))
     and then (for all J in Index_Type =>
                 (if Model (F, Root) (J).K and J /= V
                  then Model (F, Root) (J).A = Model (F, Root)'Old (J).A))
     and then Is_Add (Model (F, Root) (I).A, D, Model (F, Root) (V).A)
     and then
       (for all I in Index_Type =>
          (if I /= Root and Valid_Root (F'Old, I) then
               Model (F, I) = Model (F'Old, I)));

   procedure Init (F : in out Forest; Root : out Index_Type) with
     --  Insert a new node in F as a separate

     Pre  => Size (F) < Max,
     Post => Size (F) = Size (F)'Old + 1
     and not Valid_Root (F'Old, Root)
     and Valid_Root (F, Root)
     and (for all I in Index_Type => Parent (F, I) = Parent (F'Old, I))
     and (for all I in Index_Type =>
            (if Parent (F, I) /= 0 then Position (F, I) = Position (F'Old, I)))
     and (for all I in Index_Type =>
            (if Valid_Root (F'Old, I) then Valid_Root (F, I)))
     and (for all I in Index_Type =>
            (if Valid_Root (F, I) and I /= Root then Valid_Root (F'Old, I)))
     and (for all I in Index_Type =>
            (if Valid_Root (F'Old, I) then Model (F, I) = Model (F'Old, I)))
     and (for all I in Index_Type =>
            (if I /= Root then not Model (F, Root) (I).K));
private

   type Cell is record
      Left, Right, Parent : Extended_Index_Type := 0;
      Position            : Position_Type := Top;
   end record;
   type Cell_Array is array (Index_Type) of Cell;

   type Forest is record
      S : Extended_Index_Type := 0;
      C : Cell_Array;
   end record
     with Type_Invariant => Tree_Structure (Forest);

   function Tree_Structure (F : Forest) return Boolean;
   --  Invariant of the structure of the forest
end Binary_Trees;
