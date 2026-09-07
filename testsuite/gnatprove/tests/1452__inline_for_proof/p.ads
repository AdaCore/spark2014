--  Example of package introducing a deep copy function with an inline
--  annotation. As "=" is not allowed on pointers, it needs to use the logical
--  equality in its post.

package P with SPARK_Mode is
   type T is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation"),
     Annotate => (GNATprove, Predefined_Equality, "Only_Null");

   function Is_Reclaimed (X : T) return Boolean with
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   function Logical_Eq (X, Y : T) return Boolean with
     Annotate => (GNATprove, Logical_Equal);

   function Copy (X : T) return T with
     Post => Logical_Eq (Copy'Result, X),
     Annotate => (GNATprove, Inline_For_Proof);

private
   pragma Annotate (GNATprove, Hide_Info, "Private_Part");

   type T is access Integer;

   function Is_Reclaimed (X : T) return Boolean is (X = null);

   function Logical_Eq (X, Y : T) return Boolean is
      ((X = null) = (Y = null) and then (if X /= null then X.all = Y.all));
end P;
