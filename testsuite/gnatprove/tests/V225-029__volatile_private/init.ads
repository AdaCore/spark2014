package Init is
   type Parent is limited record
      null;
   end record
   with
      Async_Readers,
      Volatile;

   type Child is limited private;
   subtype Subchild is Child;

   procedure Initialize (Shared_Context : out Subchild);

private
   type Child is limited new Parent;
end Init;
