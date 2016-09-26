generic

   type State_Type is private;

package P.Duplex
is
   type Context is private;

   procedure Duplex (Ctx : out Context)
   with Depends => (Ctx => (null));

private

   type Context is record
      State : State_Type;
   end record;
end P.Duplex;
