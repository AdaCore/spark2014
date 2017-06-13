with Tasking; use Tasking;

package Type_Implicit is

   task type Worker
     with Global  => (In_Out  => Mailbox),
          Depends => (Mailbox =>+ null);

end;
