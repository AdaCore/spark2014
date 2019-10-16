with Ada.Text_IO; use Ada.Text_IO;
with Output, Pump;
use Output, Pump;

package body PumpUnit with
   SPARK_Mode    => On,
   Refined_State => (Account => (outstanding, total_pay, invariant_value),
    State => (cur_state), Children => (cur_pump, pump_one, pump_two))
is

   type internal_state is (pumping, ready, waiting, base);

   cur_state   : internal_state := base;
   cur_pump    : Pump_Record;
   total_pay   : Natural;
   outstanding : Natural;

   pump_one : Pump_Record;
   pump_two : Pump_Record;

   invariant_value : Natural;

   function get_outstanding return Natural is (outstanding) with
      Refined_Global  => (Input => outstanding),
      Refined_Depends => (get_outstanding'Result => outstanding);

   function get_total return Natural is (total_pay) with
      Refined_Global  => (Input => total_pay),
      Refined_Depends => (get_total'Result => total_pay);

   function get_cur_price return Nat_Type is (cur_pump.Price) with
      Refined_Global  => (Input => cur_pump),
      Refined_Depends => (get_cur_price'Result => cur_pump);

   function get_cur_resevoir return Nat_Type is (cur_pump.Resevoir) with
      Refined_Global  => (Input => cur_pump),
      Refined_Depends => (get_cur_resevoir'Result => cur_pump);

   function is_base return Boolean is (cur_state = base) with
      Refined_Global  => (Input => cur_state),
      Refined_Depends => (is_base'Result => cur_state);

   function is_ready return Boolean is (cur_state = ready) with
      Refined_Global  => (Input => cur_state),
      Refined_Depends => (is_ready'Result => cur_state);

   function is_waiting return Boolean is (cur_state = waiting) with
      Refined_Global  => (Input => cur_state),
      Refined_Depends => (is_waiting'Result => cur_state);

   function is_pumping return Boolean is (cur_state = pumping) with
      Refined_Global  => (Input => cur_state),
      Refined_Depends => (is_pumping'Result => cur_state);

   function current_variant return Natural
--       with
--       Global => (Input => (outstanding, total_pay, pump_one, pump_two)),
--       Depends => (current_variant'Result => (outstanding, total_pay, pump_one, pump_two)),
--       Pre => pump_one.Remaining <= Natural'Last - pump_two.Remaining and then
--       total_pay <= Natural'Last -pump_one.Remaining and then
--       outstanding <= Natural'Last - total_pay
      is
      sum : Natural;
   begin
      sum := 0;

   --sum :=outstanding + total_pay + pump_one.Remaining + pump_two.Remaining;
      -- could not get pre conditions to make sure there were no overflows
      return sum;
   end current_variant;

   function till_invariant return Boolean is
     (current_variant = invariant_value);
--     with
--       Refined_Global => (Input => (outstanding, invariant_value, total_pay, pump_one, pump_two)),
--       Refined_Depends => (till_invariant'Result => (outstanding, invariant_value, total_pay, pump_one, pump_two));

   procedure Initialize with
      Refined_Global =>
      (Output =>
         (pump_one, pump_two, cur_state, cur_pump, outstanding, total_pay,
          invariant_value)),
      Refined_Depends => (pump_one => null, pump_two => null,
       cur_state => null, cur_pump => null, outstanding => null,
       total_pay => null, invariant_value => null)
   is

   begin
      pump_one.Name := "Petrol____";
      pump_two.Name := "Diesel____";

      pump_one.Resevoir := 140;
      pump_two.Resevoir := 120;

      pump_one.Price := 2;
      pump_two.Price := 2;

      pump_one.Remaining := 280;
      pump_two.Remaining := 240;

      cur_state   := base;
      cur_pump    := pump_one;
      outstanding := 0;
      total_pay   := 0;

      invariant_value := current_variant;
   end Initialize;

   procedure start_pumping with
      SPARK_Mode,
      Refined_Global  => (In_out => (cur_state, outstanding, cur_pump)),
      Refined_Depends => (cur_state => cur_state,
       ((outstanding)) => +(cur_pump, cur_state),
       cur_pump        => (cur_pump, cur_state))
   is
   begin
      if is_ready then
         cur_state         := pumping;
         outstanding       := outstanding + cur_pump.Price;
         cur_pump.Resevoir := cur_pump.Resevoir - 1;
         Output.pump (cur_pump.Name, 1);
      end if;
   end start_pumping;

   procedure stop_pumping with
      Refined_Global  => (In_Out => cur_state),
      Refined_Depends => (cur_state => cur_state)
   is
   begin
      if (cur_state = pumping) then
         cur_state := ready;
      end if;

   end stop_pumping;

   procedure replace_nozel with
      Refined_Global  => (In_Out => cur_state),
      Refined_Depends => (cur_state => cur_state)
   is
   begin
      if is_ready then
         cur_state := waiting;
      end if;
   end replace_nozel;

   procedure lift_nozel (pump_index : in Integer) with
      Refined_Global => (Input => (pump_one, pump_two), Output => (cur_pump),
       In_Out => cur_state),
      Refined_Depends => (cur_pump => (pump_index, pump_one, pump_two),
       cur_state => cur_state)

   is
   begin
      if (pump_index < 2) then
         cur_pump := pump_one;
      else
         cur_pump := pump_two;
      end if;

      -- this has to be the case so that it's initialized but doesn't meet
      -- requirement that pump isn't lifted when outside waiting or base state
      if cur_state = waiting or else cur_state = base then
         cur_state := ready;
      end if;
   end lift_nozel;

   procedure pay with
      Refined_Global  => (In_Out => (total_pay, outstanding, cur_state)),
      Refined_Depends => (total_pay => (outstanding, cur_state, total_pay),
       cur_state => cur_state, outstanding => +cur_state)
   is
   begin
      if (is_waiting) then
         total_pay := total_pay + outstanding;
         cur_state := base;
         Output.pay (outstanding);
         outstanding := 0;
      end if;

   end pay;

end PumpUnit;
