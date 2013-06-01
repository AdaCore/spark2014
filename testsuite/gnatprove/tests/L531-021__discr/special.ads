with Basic;

package Special is

   -- specialize using a subtype
   subtype Sp is Basic.R (Basic.A);

   procedure P (V : in out Sp);

   -- specialize on assignment (in subprogram body)
   procedure T;
end Special;
