#ifndef MESSAGE_H
#define MESSAGE_H

   #include <stddef.h>

   typedef unsigned short nodeid_t;      // 16 bit network node ID numbers.
   typedef unsigned long  sequenceno_t;  // 32 bit packet sequence numbers.

   struct PacketHeader {
       nodeid_t     source_node;
       nodeid_t     destination_node;
       sequenceno_t sequence_number;
   };

   enum error_code {
       SUCCESS = 1, INVALID_DESTINATION, INSUFFICIENT_SPACE
   };

   // Returns the Fletcher checksum of the given buffer.
   unsigned short compute_fletcher_checksum(const char *buffer, size_t size);

   // Installs the given header into the buffer. Returns an error code as
   // appropriate. If an error is detected the buffer is left unchanged.
   enum error_code install_header(
       char *buffer,
       size_t size,
       const struct PacketHeader *header);

#endif
