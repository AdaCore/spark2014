with Interfaces;   use Interfaces;
with Interfaces.C; use Interfaces.C;
-- with os_arch;      use os_arch;

package body test
   with SPARK_mode
is

   -----------------
   -- Private API --
   -----------------

   -------------------
   -- Private types --
   -------------------

   OS_MAX_MBX_CNT      : constant := 3;

   type os_mbx_index_t is mod OS_MAX_MBX_CNT;

   subtype os_mbx_count_t is types.uint8_t range 0 .. OS_MAX_MBX_CNT;

   type os_mbx_t_array is array (os_mbx_index_t) of os_mbx_entry_t;

   type os_mbx_t is record
      head             : os_mbx_index_t;
      count            : os_mbx_count_t;
      mbx_array        : os_mbx_t_array;
   end record;

   type os_task_rw_t is record
      next             : os_task_id_t;
      prev             : os_task_id_t;
      mbx_waiting_mask : os_mbx_mask_t;
   end record;

   -----------------------
   -- Private variables --
   -----------------------

   ---------------------
   -- os_task_list_rw --
   ---------------------

   os_task_list_rw : array (os_task_id_param_t) of os_task_rw_t;

   ---------------------
   -- os_task_mbx_rw --
   ---------------------

   os_task_mbx_rw : array (os_task_id_param_t) of os_mbx_t;

   ---------------------
   -- os_task_current --
   ---------------------
   --  This variable holds the ID of the current elected task.

   os_task_current : os_task_id_param_t;

   -----------------------------
   -- os_task_ready_list_head --
   -----------------------------
   --  This variable holds the ID of the first task in the ready list (the
   --  next one that will be elected).
   --  Note: Its value could be OS_TASK_ID_NONE if no task is ready.

   os_task_ready_list_head : os_task_id_t;

   ----------------------------------
   -- Private functions/procedures --
   ----------------------------------

   ----------------------
   -- + os_mbx_index_t --
   ----------------------
   -- add operator overload for os_mbx_index_t

   function "+" (Left  : os_mbx_index_t;
                 Right : os_mbx_count_t) return os_mbx_index_t
   is (Left + os_mbx_index_t'Mod (Right));

   -----------------------------
   -- os_mbx_get_waiting_mask --
   -----------------------------
   --  Get a mask of task the given task is waiting mbx from

   function os_mbx_get_waiting_mask
     (task_id : os_task_id_param_t) return os_mbx_mask_t
   is (os_task_list_rw (task_id).mbx_waiting_mask);

   ---------------------
   -- os_mbx_is_empty --
   ---------------------
   --  Check if the mbx fifo of a given task is empty.

   function os_mbx_is_empty (task_id : os_task_id_param_t) return Boolean
   is (os_task_mbx_rw (task_id).count = os_mbx_count_t'First);

   -------------------------
   -- os_mbx_get_mbx_head --
   -------------------------
   --  Retrieve the mbx head index of the given task.

   function os_mbx_get_mbx_head
     (task_id : os_task_id_param_t) return os_mbx_index_t
   is (os_task_mbx_rw (task_id).head);

   -------------------------
   -- os_mbx_inc_mbx_head --
   -------------------------
   --  Increment the mbx head index of the given task.
   --  No contract, it will be inlined

   procedure os_mbx_inc_mbx_head (task_id : os_task_id_param_t)
   is
   begin
      os_task_mbx_rw (task_id).head :=
              os_mbx_index_t'Succ (os_mbx_get_mbx_head (task_id));
   end os_mbx_inc_mbx_head;

   --------------------------
   -- os_mbx_get_mbx_count --
   --------------------------
   --  Retrieve the mbx count of the given task.

   function os_mbx_get_mbx_count
     (task_id : os_task_id_param_t) return os_mbx_count_t
   is (os_task_mbx_rw (task_id).count);

   -------------------------
   -- os_mbx_get_mbx_tail --
   -------------------------
   --  Retrieve the mbx tail index of the given task.

   function os_mbx_get_mbx_tail
     (task_id : os_task_id_param_t) return os_mbx_index_t
   is (os_mbx_get_mbx_head (task_id) +
       os_mbx_count_t'Pred (os_mbx_get_mbx_count (task_id)))
   with
      Global => (Input => os_task_mbx_rw),
      Pre => not os_mbx_is_empty (task_id);

   --------------------------
   -- os_mbx_dec_mbx_count --
   --------------------------
   --  Decrement the mbx count of the given task.

   procedure os_mbx_dec_mbx_count (task_id : os_task_id_param_t)
   with
      Global => (In_Out => os_task_mbx_rw),
      Pre => (not os_mbx_is_empty (task_id)),
      Post => os_task_mbx_rw = os_task_mbx_rw'Old'Update (task_id => os_task_mbx_rw'Old (task_id)'Update (count => os_task_mbx_rw'Old (task_id).count - 1))
   is
   begin
      os_task_mbx_rw (task_id).count :=
              os_mbx_count_t'Pred (os_mbx_get_mbx_count (task_id));
   end os_mbx_dec_mbx_count;

   ---------------------------------
   -- os_mbx_get_mbx_entry_sender --
   ---------------------------------

   function os_mbx_get_mbx_entry_sender
     (task_id   : os_task_id_param_t;
      index : os_mbx_count_t) return os_task_id_param_t
   is (os_task_id_param_t (os_task_mbx_rw (task_id).mbx_array
           (os_mbx_get_mbx_head (task_id) + index).sender_id))
   with
      Global => (Input => (os_task_mbx_rw)),
      Pre => os_task_mbx_rw (task_id).mbx_array
                  (os_mbx_get_mbx_head (task_id) + index).sender_id
                  in os_task_id_param_t;

   ----------------------------
   -- os_mbx_clear_mbx_entry --
   ----------------------------
   --  No contract, it will be inlined

   procedure os_mbx_clear_mbx_entry
     (task_id   : os_task_id_param_t;
      mbx_index : os_mbx_index_t)
   is
   begin
      os_task_mbx_rw (task_id).mbx_array (mbx_index).sender_id :=
                                                               OS_TASK_ID_NONE;
      os_task_mbx_rw (task_id).mbx_array (mbx_index).msg := 0;
   end os_mbx_clear_mbx_entry;

   --------------------------
   -- os_mbx_set_mbx_entry --
   --------------------------
   --  No contract, it will be inlined

   procedure os_mbx_set_mbx_entry
     (task_id   : os_task_id_param_t;
      index : os_mbx_count_t;
      mbx_entry : os_mbx_entry_t)
   is
   begin
      os_task_mbx_rw (task_id).mbx_array (os_mbx_get_mbx_head (task_id) + index) := mbx_entry;
   end os_mbx_set_mbx_entry;

   --------------------------
   -- os_mbx_get_mbx_entry --
   --------------------------

   function os_mbx_get_mbx_entry
     (task_id   : os_task_id_param_t;
      index : os_mbx_count_t) return os_mbx_entry_t
   is (os_task_mbx_rw (task_id).mbx_array (os_mbx_get_mbx_head (task_id) + index));

   ---------------------------------
   -- os_mbx_is_waiting_mbx_entry --
   ---------------------------------

   function os_mbx_is_waiting_mbx_entry
     (task_id   : os_task_id_param_t;
      index : os_mbx_count_t) return Boolean
   is ((os_mbx_get_waiting_mask (task_id) and
        os_mbx_mask_t (Shift_Left
                (Unsigned_32'(1), Natural (os_mbx_get_mbx_entry_sender
                (task_id, index))))) /= 0)
   with
      Global => (Input => (os_task_list_rw, os_task_mbx_rw)),
      Pre => not os_mbx_is_empty (task_id) and then
             os_ghost_mbx_are_well_formed and then
             index < os_mbx_get_mbx_count (task_id) and then
             os_mbx_get_mbx_entry_sender (task_id, index) in os_task_id_param_t;

   ----------------------
   --  Ghost functions --
   ----------------------

   ---------------------------------------
   -- os_ghost_task_mbx_are_well_formed --
   ---------------------------------------
   --  mbx are circular FIFO (contained in an array) where head is the index
   --  of the fisrt element of the FIFO and count is the number of element
   --  stored in the FIFO.
   --  When an element of the FIFO is filled its sender_id field needs to be
   --  >= 0. When an element in the circular FIFO is empty, its sender_if field
   --  is -1 (OS_TASK_ID_NONE).
   --  So this condition makes sure that all non empty element of the circular
   --  FIFO have sender_id >= 0 and empty elements of the FIFO have sender_id
   --  = -1.
   --  Note: Here we have to duplicate the function code in the post condition
   --  in order to be able to support the pragma Inline_For_Proof required
   --  to help the prover in os_ghost_mbx_are_well_formed() function below.

   function os_ghost_task_mbx_are_well_formed (task_id : os_task_id_param_t) return Boolean is
      (for all index in os_mbx_index_t'Range =>
         (if (os_mbx_count_t(index) >= os_mbx_get_mbx_count (task_id))
          then (os_task_mbx_rw (task_id).mbx_array (os_mbx_get_mbx_head (task_id) + os_mbx_count_t (index)).sender_id = OS_TASK_ID_NONE)
          else (os_task_mbx_rw (task_id).mbx_array (os_mbx_get_mbx_head (task_id) + os_mbx_count_t (index)).sender_id in os_task_id_param_t)))
   with
      Ghost => true;
      pragma Annotate (GNATprove, Inline_For_Proof,
                       os_ghost_task_mbx_are_well_formed);

   ----------------------------------
   -- os_ghost_mbx_are_well_formed --
   ----------------------------------

   function os_ghost_mbx_are_well_formed return Boolean is
      (for all task_id in os_task_id_param_t'Range =>
         os_ghost_task_mbx_are_well_formed (task_id));

   ----------------
   -- Public API --
   ----------------

   ----------------------------------
   -- os_sched_get_current_task_id --
   ----------------------------------

   function os_sched_get_current_task_id return os_task_id_param_t
   is (os_task_current);

   -----------------------------
   -- os_mbx_remove_first_mbx --
   -----------------------------

   procedure os_mbx_remove_first_mbx
      (task_id    : in os_task_id_param_t)
   with
      Global => (In_Out => os_task_mbx_rw),
      Pre => (not os_mbx_is_empty (task_id)) and os_ghost_mbx_are_well_formed,
      Post => (os_task_mbx_rw = os_task_mbx_rw'Old'Update (task_id => os_task_mbx_rw'Old (task_id)'Update (count => os_mbx_count_t'Pred (os_task_mbx_rw'Old (task_id).count), head => os_mbx_index_t'Succ (os_task_mbx_rw'Old (task_id).head), mbx_array => os_task_mbx_rw'Old (task_id).mbx_array'Update (os_mbx_index_t'Pred (os_mbx_get_mbx_head (task_id)) => (sender_id => OS_TASK_ID_NONE, msg => 0)))))
   is
      mbx_index   : constant os_mbx_index_t := os_mbx_get_mbx_head (task_id);
   begin
      --  remove the first mbx from the mbx queue
      --  (by clearing the entry).
      os_mbx_clear_mbx_entry (task_id, mbx_index);

      --  We just increase the mbx head
      os_mbx_inc_mbx_head (task_id);

      --  decrement the mbx count
      os_mbx_dec_mbx_count (task_id);
   end os_mbx_remove_first_mbx;

   --------------------
   -- os_mbx_receive --
   --------------------

   procedure os_mbx_receive
     (status    : out os_status_t;
      mbx_entry : out os_mbx_entry_t)
   is
      --  retrieve current task id
      current   : constant os_task_id_param_t := os_sched_get_current_task_id;
   begin
      mbx_entry.sender_id := OS_TASK_ID_NONE;
      mbx_entry.msg       := 0;

      if os_mbx_is_empty (current) then
         --  mbx queue is empty, so we return with error
         status := OS_ERROR_FIFO_EMPTY;
      else
         --  initialize status to error in case we don't find a mbx.
         status := OS_ERROR_RECEIVE;

         --  go through received mbx for the current task
         for iterator in 0 ..
                         os_mbx_count_t'Pred (os_mbx_get_mbx_count (current)) loop

            pragma Loop_Invariant (os_ghost_mbx_are_well_formed and
                                   (not os_mbx_is_empty (current)));
            -- pragma Loop_Invariant (os_task_mbx_rw = os_task_mbx_rw'Loop_Entry);

	    -- pragma assert (iterator < os_mbx_get_mbx_count (current));

            --  is this a mbx we are waiting for
            if os_mbx_is_waiting_mbx_entry (current, iterator) then

               --  copy the mbx into the task mbx entry
               mbx_entry := os_mbx_get_mbx_entry (current, iterator);

               os_mbx_remove_first_mbx (current);

               --  We found a matching mbx
               status := OS_SUCCESS;

               --  Exit the for loop as we found a mbx we were
               --  waiting for.
               exit;
            end if;
         end loop;
      end if;
   end os_mbx_receive;

end test;
