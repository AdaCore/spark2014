#include <string.h>
#include "message.h"

// Returns the Fletcher checksum of the given buffer.
unsigned short compute_fletcher_checksum(const char *buffer, size_t size)
{
    unsigned short sum1 = 0;
    unsigned short sum2 = 0;
    size_t index;

    for (index = 0; index < size; ++index) {
        sum1 = (sum1 + buffer[index]) % 255;
        sum2 = (sum2 + sum1) % 255;
    }
    return (sum2 << 8) | sum1;
}


// Installs the given header into the buffer. Returns an error code as appropriate.
enum error_code install_header(char *buffer, size_t size, const struct PacketHeader *header)
{
    enum error_code status = SUCCESS;

    // Check high priority errors last to override low priority errors.
    if (header->source_node == header->destination_node) {
        status = INVALID_DESTINATION;
    }
    if (size < 12) {
        status = INSUFFICIENT_SPACE;
    }

    if (status == SUCCESS) {
        // Signature is 0xDEADBEEF (little endian order).
        buffer[0] = 0xEF;
        buffer[1] = 0xBE;
        buffer[2] = 0xAD;
        buffer[3] = 0xDE;

        // We are assuming the values have appropriate endianness already.
        memcpy(buffer + 4, &header->source_node, 2);
        memcpy(buffer + 6, &header->destination_node, 2);
        memcpy(buffer + 8, &header->sequence_number, 4);
    }
    return status;
}


// This function created to make install_header SPARK callable.
void install_header_helper(
    char *buffer,
    size_t size,
    const struct PacketHeader *header,
    enum error_code *status)
{
    enum error_code result = install_header(buffer, size, header);
    *status = result;
}

