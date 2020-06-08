pragma Unevaluated_Use_Of_Old (Allow);
with Pump; use Pump;
package PumpUnit with
   SPARK_Mode     => On,
   Abstract_State => (Account,   -- amount currently owing, total amount accrued
                      State,     -- physical state of the unit
                      Children), -- Pumps which make up the unit
   Initializes       => State,
   Initial_Condition => is_base
   -- just have one state Abstract_State => State

is
   type Pump_Array_Type is array (Integer range 1 .. 2) of Pump_Record;

   function get_outstanding return Natural with
      Global  => (Input => Account),
      Depends => (get_outstanding'Result => Account);

   function get_total return Natural with
      Global  => (Input => Account),
      Depends => (get_total'Result => Account);

   function get_cur_price return Nat_Type with
      Global  => (Input => Children),
      Depends => (get_cur_price'Result => Children);

   function get_cur_resevoir return Nat_Type with
      Global  => (Input => Children),
      Depends => (get_cur_resevoir'Result => Children);

   function is_waiting return Boolean with
      Global  => (Input => State),
      Depends => (is_waiting'Result => State);

   function is_ready return Boolean with
      Global  => (Input => State),
      Depends => (is_ready'Result => State);

   function is_pumping return Boolean with
      Global  => (Input => State),
      Depends => (is_pumping'Result => State);

   function is_base return Boolean with
      Global  => (Input => State),
      Depends => (is_base'Result => State);

   function till_invariant return Boolean;
--       Global => (Input => (Account, Children)),
--       Depends => (till_invariant'Result => (Account, Children));

   -- for checking that the sum of money received and potential money is
   -- constant.

   procedure start_pumping with
      Global  => (In_Out => (State, Account, Children)),
      Depends => (State => State, Account => +(Children, State),
       Children => +State),
      Pre => is_ready and then get_outstanding < Natural'Last - get_cur_price
      and then get_cur_resevoir > Nat_Type'First,
      Post => is_pumping
      and then get_outstanding = get_outstanding'Old + get_cur_price
      and then get_cur_resevoir = get_cur_resevoir'Old - 1;

   procedure stop_pumping with
      Global  => (In_Out => State),
      Depends => (State => State),
      Pre     => is_pumping,
      Post    => is_ready;

   procedure lift_nozel (pump_index : in Integer) with
      Global  => (In_Out => (Children, State)),
      Depends => (Children =>+ (pump_index), State =>State),
      Pre     => (is_base or else is_waiting)
      and then pump_index in Pump_Array_Type'Range,
      Post => is_ready;

   procedure replace_nozel with
      Global  => (In_Out => State),
      Depends => (State => State),
      Pre     => is_ready,
      Post    => is_waiting;

   procedure pay with
      Global  => (In_Out => (Account, State)),
      Depends => (Account => (Account, State), State => State),
      Pre => is_waiting and then get_total < Natural'Last - get_outstanding,
      Post    => is_base and then get_total = get_total'Old + get_outstanding;
      -- not sure why this doesn't pass, do I need an assertion in the body to
      -- enforce the pre condition ?

   procedure Initialize with
      Global  => (Output => (State, Account, Children)),
      Depends => (Children => null, State => null, Account => null);

private

end PumpUnit;
