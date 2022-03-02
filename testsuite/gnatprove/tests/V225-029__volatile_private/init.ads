with Context;

package Init is
   type Raw_Shared_Context_Type is limited private;
   subtype Shared_Context_Type is Raw_Shared_Context_Type;

   procedure Initialize (Shared_Context : out Shared_Context_Type);

private
   type Raw_Shared_Context_Type is limited new Context.Raw_Context_Type;
end Init;
