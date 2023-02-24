
package Iterable_Invariant with SPARK_Mode is
   type Container is private
     with Iterable => (First       => First,
                       Next        => Next,
                       Has_Element => Has_Element,
                       Element     => Element);
   type Cursor is private;

   function First (C : Container) return Cursor;
   function Next (C : Container; X : Cursor) return Cursor
     with Pre => Has_Element (C, X);
   function Has_Element (C : Container; X : Cursor) return Boolean;
   function Element (C : Container; X : Cursor) return Boolean;

   procedure Allowed_Quantification (C : Container)
     with Post =>
       Has_Element (C, First (C))
       and then not Element (C, First(C))
       and then Has_Element (C, Next (C, First (C)))
       and then Element (C, Next (C, First (C)))
       and then
       (for all X of C => --@INVARIANT_CHECK:PASS
          (for all Y of C => --@INVARIANT_CHECK:PASS
             (X and Y) or (not X) or (not Y)));

private
   type Container is (Correct_Value, Invalid_Value)
     with Type_Invariant => Container /= Invalid_Value,
       Default_Value => Correct_Value;
   type Cursor is range 0 .. 2;

   procedure Forbidden_Quantification (C : Container)
     with Pre => (for all X of C => True), --@INVARIANT_CHECK:FAIL
     Post => C = Invalid_Value;

end Iterable_Invariant;
