package Red_Black_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Red_Or_Black is (Red, Black);

   type Tree_Cell;

   type Tree is access Tree_Cell;

   type Tree_Cell is record
      Value : Integer;
      Color : Red_Or_Black;
      Left  : Tree;
      Right : Tree;
   end record;

   ------------------------------------------------
   -- Model of the tree : A sequence of integers --
   ------------------------------------------------

   function Size (X : access constant Tree_Cell) return Natural is
     (if X = null then 0
      elsif Size (X.Left) < Natural'Last - Size (X.Right)
      then Size (X.Left) + Size (X.Right) + 1
      else Natural'Last)
   with Annotate => (GNATprove, Terminating);
   --  Number of elements in the tree

   pragma Annotate
     (GNATprove, False_Positive, """Size"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   type Model_Type is array (Positive range <>) of Integer with Ghost;

   function "=" (X, Y : Model_Type) return Boolean is
     (X'First = Y'First and then X'Length = Y'Length
      and then (for all I in X'Range => X (I) = Y (I)))
   with Ghost;
   --  Redefine equality to also take bounds into account

   function Is_Concat (X1 : Model_Type; I2 : Integer; X3 : Model_Type; R : Model_Type) return Boolean is
     (X1'First = R'First and then X1'Length = R'Length - X3'Length - 1
      and then (if X3'Length > 0 then X3'First = X1'First + X1'Length + 1)
      and then (for all I in X1'Range => X1 (I) = R (I))
      and then R (X1'First + X1'Length) = I2
      and then (for all I in X3'Range => X3 (I) = R (I)))
   with Ghost;
   --  Returns true if R is X1 & I2 & X3. No sliding are allowed, X3 should
   --  start at the end of X1 plus 1.

   function Model (X : access constant Tree_Cell; Fst : Positive) return Model_Type
   with Ghost,
     Pre  => Size (X) <= Natural'Last - Fst,
     Post => Model'Result'First = Fst and then Model'Result'Length = Size (X)
     and then
       (if X /= null then
          Is_Concat (Model (X.Left, Fst),
                     X.Value,
                     Model (X.Right, Fst + Size (X.Left) + 1),
                     Model'Result)),
     Annotate => (GNATprove, Terminating);
   --  A model of a tree is an array containing the values of X in order. We
   --  first traverse the left subtree, then the root, and then the right
   --  subtree.

   pragma Annotate
     (GNATprove, False_Positive, """Model"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Model (X : access constant Tree_Cell) return Model_Type is
      (Model (X, 1))
   with Ghost,
     Pre  => Size (X) < Natural'Last,
     Post => Model'Result'First = 1 and then Model'Result'Length = Size (X);

   --------------------------
   -- Properties of Models --
   --------------------------

   function Is_Sorted (T : Model_Type) return Boolean is
      (for all I in T'Range =>
         (for all J in T'Range => (if I < J then T (I) < T (J))))
   with Ghost;
   --  Whether a model is sorted

   function Contains (T : Model_Type; V : Integer) return Boolean is
      (for some I in T'Range => T (I) = V)
   with Ghost;
   --  Inclusion in a model

   function Model_Insert (T : Model_Type; V : Integer; R : Model_Type) return Boolean is
     (Contains (R, V)
      and (for all J in T'Range => Contains (R, T (J)))
      and (for all J in R'Range => R (J) = V or Contains (T, R (J))))
   with Ghost;
   --  Whether a model R is the result of inserting V inside T

   ----------------
   --  Balancing --
   ----------------

   function Nb_Black (T : access constant Tree_Cell) return Natural is
     (if T = null then 0
      elsif T.Color = Red then Nb_Black (T.Left)
      else Nb_Black (T.Left) + 1) with
     Pre  => Size (T) < Natural'Last,
     Post => Nb_Black'Result <= Size (T),
     Annotate => (GNATprove, Terminating);
   --  Number of black nodes in the left most branch of T

   pragma Annotate
     (GNATprove, False_Positive, """Nb_Black"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Same_Nb_Black (T : access constant Tree_Cell) return Boolean is
     (T = null
      or else (Nb_Black (T.Left) = Nb_Black (T.Right)
               and then Same_Nb_Black (T.Left)
               and then Same_Nb_Black (T.Right)))
   with Ghost,
     Pre => Size (T) < Natural'Last,
     Annotate => (GNATprove, Terminating);
   --  All branches of T contain the same number of black nodes

   pragma Annotate
     (GNATprove, False_Positive, """Same_Nb_Black"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Get_Color (T : access constant Tree_Cell) return Red_Or_Black is
     (if T = null then Black else T.Color);
   --  Color of the root of a tree. If the tree is empty, it is assimilated to
   --  a black node.

   function Scarce_Red (T : access constant Tree_Cell) return Boolean is
     (T = null
      or else
        ((if T.Color = Red then Get_Color (T.Left) = Black
          and then Get_Color (T.Right) = Black)
         and Scarce_Red (T.Left)
         and Scarce_Red (T.Right)))
   with Ghost,
     Pre => Size (T) < Natural'Last,
     Annotate => (GNATprove, Terminating);
   --  A red node is always followed by two black nodes

   pragma Annotate
     (GNATprove, False_Positive, """Scarce_Red"" might not terminate",
      "Recursive calls only occur on structuraly smaller values");

   function Balanced (T : access constant Tree_Cell) return Boolean is
     (Get_Color (T) = Black
      and then Scarce_Red (T)
      and then Same_Nb_Black (T))
   with Ghost,
     Pre => Size (T) < Natural'Last;
   --  Use colors to enforce balancing of the tree:
   --   * The root is always black
   --   * A red node can only be followed by black nodes
   --   * There are the same number of black nodes in all branches

   --------------------------
   --  Red black trees API --
   --------------------------

   function RBT_Invariant (T : access constant Tree_Cell) return Boolean is
     (Is_Sorted (Model (T)) and Balanced (T))
   with Ghost,
     Pre  => Size (T) < Natural'Last;
   --  Invariant of red black trees, they contain sorted values, and they are
   --  balanced.

   function Contains (T : access constant Tree_Cell; V : Integer) return Boolean
   with
     Pre  => Size (T) < Natural'Last and then RBT_Invariant (T),
     Post => Contains'Result = Contains (Model (T), V);

   procedure Insert (T : in out Tree; V : Integer) with
     Pre  => Size (T) < Natural'Last - 1 and then RBT_Invariant (T),
     Post => RBT_Invariant (T)
     and Size (T) in Size (T)'Old .. Size (T)'Old + 1
     and Model_Insert (Model (T)'Old, V, Model (T));

end Red_Black_Trees;
