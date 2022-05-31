pragma SPARK_Mode;

with Ada.Unchecked_Deallocation;

procedure Hole is
   type IPtr is access Integer;
   type Wrap is record
      Field : IPtr;
   end record;
   type WPtr is access Wrap;
   WP : WPtr := new Wrap'(Field => new Integer'(0));
   procedure IFree is new Ada.Unchecked_Deallocation(Integer,IPtr);
   procedure WFree is new Ada.Unchecked_Deallocation(Wrap,WPtr);
   procedure Evil(X : access Wrap)
     with Pre => X /= null;
   procedure Evil(X : access Wrap) is
      -- This borrower is not checked properly.
      Y : access Wrap := X;
      Bad : IPtr := Y.all.Field;
   begin
      IFree(Bad);
   end;
begin
   Evil(WP);
   IFree(WP.all.Field);
   WFree(WP);
end;
