procedure Main with SPARK_Mode is

   --  Use of Inline_For_Proof with equality functions that do not have the
   --  Logical_Equal annotation is not allowed.

   package P1 is
      type T is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"),
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      function Is_Reclaimed (X : T) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed");

      function Logical_Eq (X, Y : T) return Boolean with
        Import;

      function Copy (X : T) return T with
        Import,
        Post => Logical_Eq (Copy'Result, X),
        Annotate => (GNATprove, Inline_For_Proof);

   private
      pragma SPARK_Mode (Off);

      type T is access Integer;
   end P1;

   --  Same as above, but uses a post on Logical_Eq to force the marking of
   --  Copy before Logical_Eq.

   package P2 is
      type T is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"),
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");

      function Is_Reclaimed (X : T) return Boolean with
        Import,
        Annotate => (GNATprove, Ownership, "Is_Reclaimed");

      function Logical_Eq (X, Y : T) return Boolean with
        Import,
        Post =>
          (if Is_Reclaimed (Copy (X)) and Is_Reclaimed (Copy (Y))
             then Logical_Eq'Result);

      function Copy (X : T) return T with
        Import,
        Post => Logical_Eq (Copy'Result, X),
        Annotate => (GNATprove, Inline_For_Proof);

   private
      pragma SPARK_Mode (Off);

      type T is access Integer;
   end P2;


begin
   null;
end Main;
