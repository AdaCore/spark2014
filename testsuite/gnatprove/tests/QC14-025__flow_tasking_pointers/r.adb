package body R is

   protected body PT is
      entry Enter when True is
      begin
         null;
      end Enter;
   end PT;

   PO : aliased PT;
   Ptr : access PT := PO'Access;

begin
   Ptr.Enter;
end R;
