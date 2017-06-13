with Tasking; use Tasking;

package Type_Explicit is

   task type Worker
     with Global  => (In_Out  => Mailbox),
          Depends => (Mailbox =>+ null, Worker =>+ null);

end;
