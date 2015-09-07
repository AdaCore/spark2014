with Interval_Tree;

package body Interval_Tree_Wrapper
  with
    SPARK_Mode => Off
is

   -- Inserts Item into tree T.
   procedure Insert (Item   : in  Interval;
                     Status : out Status_Type) is
   begin
      Interval_Tree.Insert(Interval_Tree.Interval(Item));
      Status := Success;
   exception
      when Storage_Error =>
         Status := Insufficient_Space;
      when others =>
         Status := Logical_Error;
   end Insert;


   function Size return Natural is
   begin
      return Interval_Tree.Size;
   end Size;


   procedure Destroy is
   begin
      Interval_Tree.Destroy;
   end Destroy;

end Interval_Tree_Wrapper;
