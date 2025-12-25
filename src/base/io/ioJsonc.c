/**CFile****************************************************************

  FileName    [ioJsonc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Command processing package.]

  Synopsis    [Procedures to read JSON.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ioJsonc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "map/mio/mio.h"
#include "ioAbc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// JSON value types
typedef enum {
    JSON_NULL,
    JSON_BOOL,
    JSON_NUMBER,
    JSON_STRING,
    JSON_ARRAY,
    JSON_OBJECT
} json_type_t;

// Core structure: stores offset and length in the original string
typedef struct json_value_t_ {
    uint32_t offset;     // Offset in the JSON string
    uint32_t length;     // Length of this value
    json_type_t type;    // Type of JSON value
    uint32_t container;  // Index of the container if this is an object/array
} json_value_t;

// Key-value pair for objects
typedef struct json_pair_t_ {
    json_value_t key;    // Key (always a string)
    json_value_t value;  // Associated value
} json_pair_t;

// Dynamic array for storing pairs (objects) or values (arrays)
typedef struct json_container_t_ {
    union {
        json_pair_t *pairs;   // For objects
        json_value_t *values; // For arrays
    } data;
    uint32_t count;      // Number of elements
    uint32_t capacity;   // Allocated capacity
} json_container_t;

// Main JSON structure
typedef struct json_t_ {
    char *str;                     // The original JSON string
    uint32_t str_len;              // Length of the string
    json_value_t root;             // Root element
    json_container_t *containers;  // Array of containers
    uint32_t container_count;      // Number of containers
    uint32_t container_capacity;   // Allocated capacity
} json_t;

// Creation / destruction
json_t *        json_create(void);
void            json_destroy(json_t *json);
bool            json_load_file(json_t *json, const char *filename);

// Debug/printing helpers
void            json_print(json_t *json, FILE *fp);
void            json_print_value(json_t *json, json_value_t val, FILE *fp, int indent, bool format);
void            json_print_string(json_t *json, json_value_t val, FILE *fp);
void            json_debug_value(json_t *json, json_value_t val, int indent);

// Function prototypes
json_t* json_create(void);
void json_destroy(json_t *json);
bool json_load_file(json_t *json, const char *filename);
json_value_t json_parse_value(json_t *json, uint32_t *pos);
json_container_t* json_add_container(json_t *json);
void json_skip_whitespace(const char *str, uint32_t *pos, uint32_t len);
json_value_t json_parse_string(json_t *json, uint32_t *pos);
json_value_t json_parse_number(json_t *json, uint32_t *pos);
json_value_t json_parse_object(json_t *json, uint32_t *pos);
json_value_t json_parse_array(json_t *json, uint32_t *pos);
void json_print(json_t *json, FILE *fp);
void json_print_value(json_t *json, json_value_t val, FILE *fp, int indent, bool format);
void json_print_string(json_t *json, json_value_t val, FILE *fp);
void json_debug_value(json_t *json, json_value_t val, int indent);

extern Abc_Ntk_t * Abc_NtkFromMiniMapping( int * pArray );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Create a new JSON structure
json_t* json_create(void) {
    json_t *json = (json_t*)calloc(1, sizeof(json_t));
    if (!json) return NULL;
    
    json->container_capacity = 16;
    json->containers = (json_container_t*)calloc(json->container_capacity, sizeof(json_container_t));
    if (!json->containers) {
        free(json);
        return NULL;
    }
    
    return json;
}

// Destroy JSON structure and free memory
void json_destroy(json_t *json) {
    if (!json) return;
    
    // Free containers
    for (uint32_t i = 0; i < json->container_count; i++) {
        if (json->containers[i].data.pairs) {
            free(json->containers[i].data.pairs);
        }
    }
    free(json->containers);
    
    // Free the JSON string
    free(json->str);
    
    // Free the structure
    free(json);
}

// Skip whitespace and comments
void json_skip_whitespace(const char *str, uint32_t *pos, uint32_t len) {
    while (*pos < len) {
        // Skip whitespace
        if (str[*pos] == ' ' || str[*pos] == '\t' || 
            str[*pos] == '\n' || str[*pos] == '\r') {
            (*pos)++;
            continue;
        }
        
        // Skip single-line comments
        if (*pos + 1 < len && str[*pos] == '/' && str[*pos + 1] == '/') {
            *pos += 2;
            while (*pos < len && str[*pos] != '\n') {
                (*pos)++;
            }
            continue;
        }
        
        // Skip multi-line comments
        if (*pos + 1 < len && str[*pos] == '/' && str[*pos + 1] == '*') {
            *pos += 2;
            while (*pos + 1 < len) {
                if (str[*pos] == '*' && str[*pos + 1] == '/') {
                    *pos += 2;
                    break;
                }
                (*pos)++;
            }
            continue;
        }
        
        // Not whitespace or comment
        break;
    }
}

// Add a new container and return pointer to it
json_container_t* json_add_container(json_t *json) {
    if (json->container_count >= json->container_capacity) {
        uint32_t new_capacity = json->container_capacity * 2;
        json_container_t *new_containers = (json_container_t*)realloc(
            json->containers, new_capacity * sizeof(json_container_t));
        if (!new_containers) return NULL;
        
        json->containers = new_containers;
        json->container_capacity = new_capacity;
    }
    
    json_container_t *container = &json->containers[json->container_count];
    memset(container, 0, sizeof(json_container_t));
    json->container_count++;
    return container;
}

// Parse a JSON string
json_value_t json_parse_string(json_t *json, uint32_t *pos) {
    json_value_t val = {0};
    val.container = UINT32_MAX;
    val.type = JSON_STRING;
    val.offset = *pos;
    
    (*pos)++; // Skip opening quote
    
    while (*pos < json->str_len && json->str[*pos] != '"') {
        if (json->str[*pos] == '\\') (*pos)++; // Skip escaped character
        (*pos)++;
    }
    
    (*pos)++; // Skip closing quote
    val.length = *pos - val.offset;
    return val;
}

// Parse a JSON number
json_value_t json_parse_number(json_t *json, uint32_t *pos) {
    json_value_t val = {0};
    val.container = UINT32_MAX;
    val.type = JSON_NUMBER;
    val.offset = *pos;
    
    if (json->str[*pos] == '-') (*pos)++;
    
    while (*pos < json->str_len && 
           ((json->str[*pos] >= '0' && json->str[*pos] <= '9') ||
            json->str[*pos] == '.' || json->str[*pos] == 'e' || 
            json->str[*pos] == 'E' || json->str[*pos] == '+' || 
            json->str[*pos] == '-')) {
        (*pos)++;
    }
    
    val.length = *pos - val.offset;
    return val;
}

// Parse a JSON object
json_value_t json_parse_object(json_t *json, uint32_t *pos) {
    json_value_t val = {0};
    val.container = UINT32_MAX;
    val.type = JSON_OBJECT;
    val.offset = *pos;
    
    (*pos)++; // Skip '{'
    
    json_container_t *container = json_add_container(json);
    if (!container) return val;
    val.container = json->container_count - 1;
    container = json->containers + val.container;
    
    container->capacity = 8;
    container->data.pairs = (json_pair_t*)calloc(container->capacity, sizeof(json_pair_t));
    if (!container->data.pairs) return val;
    
    json_skip_whitespace(json->str, pos, json->str_len);
    
    while (*pos < json->str_len && json->str[*pos] != '}') {
        // Parse key
        json_value_t key = json_parse_string(json, pos);
        
        json_skip_whitespace(json->str, pos, json->str_len);
        (*pos)++; // Skip ':'
        json_skip_whitespace(json->str, pos, json->str_len);
        
        // Parse value
        json_value_t value = json_parse_value(json, pos);
        
        // Add pair to container
        container = json->containers + val.container;
        if (container->count >= container->capacity) {
            uint32_t new_capacity = container->capacity * 2;
            json_pair_t *new_pairs = (json_pair_t*)realloc(
                container->data.pairs, new_capacity * sizeof(json_pair_t));
            if (!new_pairs) return val;
            
            container->data.pairs = new_pairs;
            container->capacity = new_capacity;
        }
        
        container->data.pairs[container->count].key = key;
        container->data.pairs[container->count].value = value;
        container->count++;
        
        json_skip_whitespace(json->str, pos, json->str_len);
        if (json->str[*pos] == ',') {
            (*pos)++;
            json_skip_whitespace(json->str, pos, json->str_len);
        }
    }
    
    (*pos)++; // Skip '}'
    val.length = *pos - val.offset;
    return val;
}

// Parse a JSON array
json_value_t json_parse_array(json_t *json, uint32_t *pos) {
    json_value_t val = {0};
    val.container = UINT32_MAX;
    val.type = JSON_ARRAY;
    val.offset = *pos;
    
    (*pos)++; // Skip '['
    
    json_container_t *container = json_add_container(json);
    if (!container) return val;
    val.container = json->container_count - 1;
    container = json->containers + val.container;
    
    container->capacity = 8;
    container->data.values = (json_value_t*)calloc(container->capacity, sizeof(json_value_t));
    if (!container->data.values) return val;
    
    json_skip_whitespace(json->str, pos, json->str_len);
    
    while (*pos < json->str_len && json->str[*pos] != ']') {
        // Parse value
        json_value_t value = json_parse_value(json, pos);
        
        // Add value to container
        container = json->containers + val.container;
        if (container->count >= container->capacity) {
            uint32_t new_capacity = container->capacity * 2;
            json_value_t *new_values = (json_value_t*)realloc(
                container->data.values, new_capacity * sizeof(json_value_t));
            if (!new_values) return val;
            
            container->data.values = new_values;
            container->capacity = new_capacity;
        }
        
        container->data.values[container->count] = value;
        container->count++;
        
        json_skip_whitespace(json->str, pos, json->str_len);
        if (json->str[*pos] == ',') {
            (*pos)++;
            json_skip_whitespace(json->str, pos, json->str_len);
        }
    }
    
    (*pos)++; // Skip ']'
    val.length = *pos - val.offset;
    return val;
}

// Parse any JSON value
json_value_t json_parse_value(json_t *json, uint32_t *pos) {
    json_value_t val = {0};
    val.container = UINT32_MAX;
    
    json_skip_whitespace(json->str, pos, json->str_len);
    
    if (*pos >= json->str_len) return val;
    
    char c = json->str[*pos];
    
    if (c == '"') {
        return json_parse_string(json, pos);
    } else if (c == '{') {
        return json_parse_object(json, pos);
    } else if (c == '[') {
        return json_parse_array(json, pos);
    } else if (c == 'n') {
        val.type = JSON_NULL;
        val.offset = *pos;
        val.length = 4;
        val.container = UINT32_MAX;
        *pos += 4;
        return val;
    } else if (c == 't') {
        val.type = JSON_BOOL;
        val.offset = *pos;
        val.length = 4;
        val.container = UINT32_MAX;
        *pos += 4;
        return val;
    } else if (c == 'f') {
        val.type = JSON_BOOL;
        val.offset = *pos;
        val.length = 5;
        val.container = UINT32_MAX;
        *pos += 5;
        return val;
    } else if ((c >= '0' && c <= '9') || c == '-') {
        return json_parse_number(json, pos);
    }
    
    return val;
}

// Load JSON from file
bool json_load_file(json_t *json, const char *filename) {
    FILE *fp = fopen(filename, "rb");
    if (!fp) return false;
    
    // Get file size
    fseek(fp, 0, SEEK_END);
    long file_size = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    
    if (file_size > INT32_MAX) {
        fclose(fp);
        return false;
    }
    
    // Allocate buffer
    json->str = (char*)malloc(file_size + 1);
    if (!json->str) {
        fclose(fp);
        return false;
    }
    
    // Read file
    size_t bytes_read = fread(json->str, 1, file_size, fp);
    fclose(fp);
    
    if (bytes_read != (size_t)file_size) {
        free(json->str);
        json->str = NULL;
        return false;
    }
    
    json->str[file_size] = '\0';
    json->str_len = (uint32_t)file_size;
    json->container_count = 0;
    
    // Parse JSON
    uint32_t pos = 0;
    json->root = json_parse_value(json, &pos);
    
    return true;
}

// Helper function to print a JSON value (for debugging)
void json_debug_value(json_t *json, json_value_t val, int indent) {
    for (int i = 0; i < indent; i++) printf("  ");
    
    printf("Type: %d, Offset: %u, Length: %u, Content: '", 
           val.type, val.offset, val.length);
    
    for (uint32_t i = 0; i < val.length && i < 50; i++) {
        putchar(json->str[val.offset + i]);
    }
    if (val.length > 50) printf("...");
    printf("'\n");
}

// Print a JSON string value with proper escaping
void json_print_string(json_t *json, json_value_t val, FILE *fp) {
    fputc('"', fp);
    
    // Skip the quotes in the original string
    uint32_t start = val.offset + 1;
    uint32_t end = val.offset + val.length - 1;
    
    for (uint32_t i = start; i < end; i++) {
        char c = json->str[i];
        if (c == '\\' && i + 1 < end) {
            // Handle escape sequences
            fputc(c, fp);
            i++;
            fputc(json->str[i], fp);
        } else {
            fputc(c, fp);
        }
    }
    
    fputc('"', fp);
}

// Print a JSON value recursively
void json_print_value(json_t *json, json_value_t val, FILE *fp, int indent, bool format) {
    switch (val.type) {
        case JSON_NULL:
            fprintf(fp, "null");
            break;
            
        case JSON_BOOL:
            if (json->str[val.offset] == 't') {
                fprintf(fp, "true");
            } else {
                fprintf(fp, "false");
            }
            break;
            
        case JSON_NUMBER:
            for (uint32_t i = 0; i < val.length; i++) {
                fputc(json->str[val.offset + i], fp);
            }
            break;
            
        case JSON_STRING:
            json_print_string(json, val, fp);
            break;
            
        case JSON_ARRAY: {
            fputc('[', fp);
            
            if (val.container < json->container_count) {
                json_container_t *container = &json->containers[val.container];
                
                for (uint32_t i = 0; i < container->count; i++) {
                    if (format) {
                        fprintf(fp, "\n");
                        for (int j = 0; j < indent + 1; j++) fprintf(fp, "  ");
                    }
                    
                    json_print_value(json, container->data.values[i], fp, indent + 1, format);
                    
                    if (i < container->count - 1) {
                        fputc(',', fp);
                        if (!format) fputc(' ', fp);
                    }
                }
                
                if (format && container->count > 0) {
                    fprintf(fp, "\n");
                    for (int j = 0; j < indent; j++) fprintf(fp, "  ");
                }
            }
            
            fputc(']', fp);
            break;
        }
            
        case JSON_OBJECT: {
            fputc('{', fp);
            
            if (val.container < json->container_count) {
                json_container_t *container = &json->containers[val.container];
                
                for (uint32_t i = 0; i < container->count; i++) {
                    if (format) {
                        fprintf(fp, "\n");
                        for (int j = 0; j < indent + 1; j++) fprintf(fp, "  ");
                    }
                    
                    json_print_string(json, container->data.pairs[i].key, fp);
                    fprintf(fp, ": ");
                    json_print_value(json, container->data.pairs[i].value, fp, indent + 1, format);
                    
                    if (i < container->count - 1) {
                        fputc(',', fp);
                        if (!format) fputc(' ', fp);
                    }
                }
                
                if (format && container->count > 0) {
                    fprintf(fp, "\n");
                    for (int j = 0; j < indent; j++) fprintf(fp, "  ");
                }
            }
            
            fputc('}', fp);
            break;
        }
    }
}

// Print the entire JSON to a file
void json_print(json_t *json, FILE *fp) {
    json_print_value(json, json->root, fp, 0, true);
    fprintf(fp, "\n");
}

/**Function*************************************************************

  Synopsis    []

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Jsonc_ReadTest( char * pFileName )
{
    json_t *json = json_create();
    if (!json) {
        fprintf(stderr, "Failed to create JSON structure\n");
        return 1;
    }
    
    printf("Parsing JSONC file: %s\n", pFileName);
    if (!json_load_file(json, pFileName)) {
        fprintf(stderr, "Failed to load JSON file\n");
        json_destroy(json);
        return 1;
    }
    
    printf("JSON parsed successfully!\n");
    printf("String length: %u\n", json->str_len);
    printf("Container count: %u\n", json->container_count);

    //printf("\nRoot value:\n");
    //json_debug_value(json, json->root, 0);

 /*   
    // Print the parsed JSON to a file (without comments)
    FILE *fp = fopen(output_file, "w");
    if (fp) {
        printf("\nWriting parsed JSON to: %s\n", output_file);
        json_print(json, fp);
        fclose(fp);
        printf("Output written successfully!\n");
    } else {
        fprintf(stderr, "Failed to open output file\n");
    }
*/    
    // Also print to stdout for verification
    printf("\nParsed JSON output:\n");
    json_print(json, stdout);

    json_destroy(json);
    return 0;
}

static int Jsonc_ParseNameBit( const char * pName, char * pBase, int nBase )
{
    const char * pOpen;
    const char * pClose;
    int nCopy;
    if ( pBase && nBase > 0 )
        pBase[0] = '\0';
    if ( pName == NULL || pBase == NULL || nBase <= 1 )
        return 0;
    pOpen  = strrchr( pName, '[' );
    pClose = pOpen ? strchr( pOpen, ']' ) : NULL;
    if ( pOpen && pClose && pClose > pOpen + 1 )
    {
        nCopy = (int)(pOpen - pName);
        if ( nCopy > nBase - 1 )
            nCopy = nBase - 1;
        memcpy( pBase, pName, nCopy );
        pBase[nCopy] = '\0';
        return atoi( pOpen + 1 );
    }
    strncpy( pBase, pName, nBase - 1 );
    pBase[nBase - 1] = '\0';
    return 0;
}
static const char * Jsonc_GetPortName( Abc_Obj_t * pObj )
{
    if ( Abc_ObjIsCi(pObj) && Abc_NtkIsNetlist(pObj->pNtk) && Abc_ObjFanoutNum(pObj) )
        return Abc_ObjName( Abc_ObjFanout0(pObj) );
    if ( Abc_ObjIsCo(pObj) && Abc_NtkIsNetlist(pObj->pNtk) && Abc_ObjFaninNum(pObj) )
        return Abc_ObjName( Abc_ObjFanin0(pObj) );
    return Abc_ObjName(pObj);
}
static const char * Jsonc_GetNodeOutName( Abc_Obj_t * pObj )
{
    static char Buffer[1024];
    if ( Abc_ObjFanoutNum(pObj) )
    {
        Abc_Obj_t * pFan0 = Abc_ObjFanout0(pObj);
        if ( Abc_ObjIsNet(pFan0) || Abc_ObjIsCo(pFan0) )
            return Abc_ObjName(pFan0);
    }
    if ( Abc_ObjName(pObj) )
        return Abc_ObjName(pObj);
    snprintf( Buffer, sizeof(Buffer), "n%d", Abc_ObjId(pObj) );
    return Buffer;
}

/**Function*************************************************************

  Synopsis    []

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Jsonc_WriteTest( Abc_Ntk_t * p, char * pFileName )
{
    Vec_Ptr_t * vNodes;
    Vec_Int_t * vObj2Num;
    Abc_Obj_t * pObj;
    FILE * pFile;
    int i, Counter, Total;
    assert( Abc_NtkHasMapping(p) );
    vNodes   = Abc_NtkDfs2( p );
    vObj2Num = Vec_IntStartFull( Abc_NtkObjNumMax(p) );
    Total    = Abc_NtkPiNum(p) + Vec_PtrSize(vNodes) + Abc_NtkPoNum(p);
    pFile    = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Jsonc_WriteTest(): Cannot open output file \"%s\" for writing.\n", pFileName );
        Vec_IntFree( vObj2Num );
        Vec_PtrFree( vNodes );
        return;
    }
    fprintf( pFile, "{\n" );
    fprintf( pFile, "  \"name\": \"%s\",\n", Abc_NtkName(p) ? Abc_NtkName(p) : "" );
    fprintf( pFile, "  \"nodes\": [\n" );
    Counter = 0;
    Abc_NtkForEachPi( p, pObj, i )
    {
        char Name[1024];
        int Bit = Jsonc_ParseNameBit( Jsonc_GetPortName(pObj), Name, sizeof(Name) );
        Vec_IntWriteEntry( vObj2Num, Abc_ObjId(pObj), Counter );
        fprintf( pFile, "    {\n" );
        fprintf( pFile, "      \"type\": \"pi\",\n" );
        fprintf( pFile, "      \"name\": \"%s\",\n", Name );
        fprintf( pFile, "      \"bit\": %d\n", Bit );
        fprintf( pFile, "    }%s\n", ++Counter == Total ? "" : "," );
    }
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        Mio_Gate_t * pGate = (Mio_Gate_t *)pObj->pData;
        Mio_Pin_t * pPin;
        int k;
        assert( pGate != NULL );
        Vec_IntWriteEntry( vObj2Num, Abc_ObjId(pObj), Counter );
        fprintf( pFile, "    {\n" );
        fprintf( pFile, "      \"type\": \"%s\",\n", "instance" );
        fprintf( pFile, "      \"name\": \"%s\",\n", Mio_GateReadName(pGate) );
        fprintf( pFile, "      \"fanins\":\n" );
        fprintf( pFile, "        {\n" );
        for ( pPin = Mio_GateReadPins(pGate), k = 0; pPin; pPin = Mio_PinReadNext(pPin), k++ )
        {
            Abc_Obj_t * pFanin = Abc_ObjFanin0Ntk( Abc_ObjFanin(pObj, k) );
            int FanId = Vec_IntEntry( vObj2Num, Abc_ObjId(pFanin) );
            assert( FanId >= 0 );
            fprintf( pFile, "          \"%s\": { \"node\": %d", Mio_PinReadName(pPin), FanId );
            if ( Abc_ObjIsNode(pFanin) && pFanin->pData != NULL )
                fprintf( pFile, ", \"pin\": \"%s\"", Mio_GateReadOutName((Mio_Gate_t *)pFanin->pData) );
            fprintf( pFile, " }%s\n", Mio_PinReadNext(pPin) ? "," : "" );
        }
        fprintf( pFile, "        }\n" );
        fprintf( pFile, "    }%s\n", ++Counter == Total ? "" : "," );
    }
    Abc_NtkForEachPo( p, pObj, i )
    {
        Abc_Obj_t * pDriver = Abc_ObjFanin0Ntk( Abc_ObjFanin0(pObj) );
        char Name[1024];
        int Bit = Jsonc_ParseNameBit( Jsonc_GetPortName(pObj), Name, sizeof(Name) );
        int FanId = Vec_IntEntry( vObj2Num, Abc_ObjId(pDriver) );
        assert( FanId >= 0 );
        fprintf( pFile, "    {\n" );
        fprintf( pFile, "      \"type\": \"PO\",\n" );
        fprintf( pFile, "      \"name\": \"%s\",\n", Name );
        fprintf( pFile, "      \"bit\": %d,\n", Bit );
        fprintf( pFile, "      \"fanin\": { \"node\": %d", FanId );
        if ( Abc_ObjIsNode(pDriver) && pDriver->pData != NULL )
            fprintf( pFile, ", \"pin\": \"%s\"", Mio_GateReadOutName((Mio_Gate_t *)pDriver->pData) );
        fprintf( pFile, " }\n" );
        fprintf( pFile, "    }%s\n", ++Counter == Total ? "" : "," );
    }
    fprintf( pFile, "  ]\n" );
    fprintf( pFile, "}\n" );
    fclose( pFile );
    Vec_IntFree( vObj2Num );
    Vec_PtrFree( vNodes );
}



/**Function*************************************************************

  Synopsis    []

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static json_container_t * Jsonc_GetContainer( json_t * pJson, json_value_t value )
{
    if ( value.container == UINT32_MAX )
        return NULL;
    if ( value.container >= pJson->container_count )
        return NULL;
    return pJson->containers + value.container;
}
static int Jsonc_StringEqual( json_t * pJson, json_value_t value, const char * pStr )
{
    uint32_t Len;
    if ( value.type != JSON_STRING || value.length < 2 )
        return 0;
    Len = value.length - 2;
    return strlen(pStr) == Len && strncmp( pJson->str + value.offset + 1, pStr, Len ) == 0;
}
static char * Jsonc_StringDup( json_t * pJson, json_value_t value )
{
    char * pRes;
    uint32_t i, Len;
    if ( value.type != JSON_STRING || value.length < 2 )
        return NULL;
    Len = value.length - 2;
    pRes = ABC_ALLOC( char, Len + 1 );
    for ( i = 0; i < Len; i++ )
    {
        char c = pJson->str[value.offset + 1 + i];
        if ( c == '\\' && i + 1 < Len )
        {
            i++;
            c = pJson->str[value.offset + 1 + i];
        }
        pRes[i] = c;
    }
    pRes[Len] = '\0';
    return pRes;
}
static int Jsonc_ParseInt( json_t * pJson, json_value_t value, int * pResult )
{
    char * pBuffer, * pEnd;
    uint32_t Len;
    long Temp;
    if ( value.type != JSON_NUMBER )
        return 0;
    Len = value.length;
    pBuffer = ABC_ALLOC( char, Len + 1 );
    memcpy( pBuffer, pJson->str + value.offset, Len );
    pBuffer[Len] = '\0';
    Temp = strtol( pBuffer, &pEnd, 10 );
    ABC_FREE( pBuffer );
    if ( pEnd == NULL || pEnd == pBuffer )
        return 0;
    *pResult = (int)Temp;
    return 1;
}
static json_value_t * Jsonc_ObjectLookup( json_t * pJson, json_value_t object, const char * pKey )
{
    json_container_t * pCont;
    uint32_t i;
    if ( object.type != JSON_OBJECT )
        return NULL;
    pCont = Jsonc_GetContainer( pJson, object );
    if ( pCont == NULL )
        return NULL;
    for ( i = 0; i < pCont->count; i++ )
        if ( Jsonc_StringEqual( pJson, pCont->data.pairs[i].key, pKey ) )
            return &pCont->data.pairs[i].value;
    return NULL;
}
static Vec_Int_t * Jsonc_NameCounts( Vec_Ptr_t * vBases, Vec_Int_t ** pvBaseIds )
{
    Abc_Nam_t * pNames;
    Vec_Int_t * vCounts, * vBaseIds;
    char * pBase;
    int i, Id;
    pNames   = Abc_NamStart( Vec_PtrSize(vBases) + 1, 24 );
    vCounts  = Vec_IntAlloc( Vec_PtrSize(vBases) + 1 );
    vBaseIds = Vec_IntAlloc( Vec_PtrSize(vBases) + 1 );
    Vec_IntFillExtra( vCounts, 1, 0 );
    Vec_PtrForEachEntry( char *, vBases, pBase, i )
    {
        int fFound;
        Id = Abc_NamStrFindOrAdd( pNames, pBase, &fFound );
        Vec_IntFillExtra( vCounts, Id + 1, 0 );
        Vec_IntAddToEntry( vCounts, Id, 1 );
        Vec_IntPush( vBaseIds, Id );
    }
    Abc_NamDeref( pNames );
    *pvBaseIds = vBaseIds;
    return vCounts;
}
static void Jsonc_AppendName( Vec_Str_t * vNames, const char * pBase, int Bit, int fUseBit )
{
    int nSize = (int)strlen(pBase ? pBase : "") + 32;
    char * pBuffer = ABC_ALLOC( char, nSize );
    if ( fUseBit )
        snprintf( pBuffer, nSize, "%s[%d]", pBase ? pBase : "", Bit );
    else
        snprintf( pBuffer, nSize, "%s", pBase ? pBase : "" );
    Vec_StrPrintStr( vNames, pBuffer );
    Vec_StrPush( vNames, '\0' );
    ABC_FREE( pBuffer );
}
static void Jsonc_AppendPortNames( Vec_Str_t * vNames, Vec_Ptr_t * vBases, Vec_Int_t * vBits )
{
    Vec_Int_t * vCounts, * vBaseIds;
    char * pBase;
    int i, Bit, Count;
    vCounts = Jsonc_NameCounts( vBases, &vBaseIds );
    Vec_PtrForEachEntry( char *, vBases, pBase, i )
    {
        Bit   = Vec_IntEntry( vBits, i );
        Count = Vec_IntEntry( vCounts, Vec_IntEntry( vBaseIds, i ) );
        Jsonc_AppendName( vNames, pBase, Bit, Bit != 0 || Count > 1 );
    }
    Vec_IntFree( vCounts );
    Vec_IntFree( vBaseIds );
}
static Vec_Int_t * Jsonc_ConvertToMiniMapping( json_t * pJson, Mio_Library_t * pLib, char ** ppDesignName )
{
    Vec_Ptr_t * vPiBases = NULL, * vPoBases = NULL;
    Vec_Int_t * vPiBits = NULL, * vPoBits = NULL;
    Vec_Int_t * vNodeMap = NULL, * vGateIdx = NULL, * vPoIdx = NULL;
    Vec_Int_t * vMapping = NULL, * vPoDrivers = NULL;
    Vec_Str_t * vNames = NULL;
    json_container_t * pNodes;
    json_value_t * pTemp;
    char * pBase;
    int i, k, nCis = 0, nNodes = 0, nCos = 0;
    int fSuccess = 0;
    if ( ppDesignName )
        *ppDesignName = NULL;
    if ( pLib == NULL )
    {
        printf( "Genlib library is not available.\n" );
        return NULL;
    }
    if ( pJson->root.type != JSON_OBJECT )
    {
        printf( "JSONC root should be an object.\n" );
        return NULL;
    }
    pTemp = Jsonc_ObjectLookup( pJson, pJson->root, "name" );
    if ( pTemp && ppDesignName && pTemp->type == JSON_STRING )
        *ppDesignName = Jsonc_StringDup( pJson, *pTemp );
    pTemp = Jsonc_ObjectLookup( pJson, pJson->root, "nodes" );
    if ( pTemp == NULL || pTemp->type != JSON_ARRAY )
    {
        printf( "JSONC file is missing top-level \"nodes\" array.\n" );
        return NULL;
    }
    pNodes = Jsonc_GetContainer( pJson, *pTemp );
    if ( pNodes == NULL )
    {
        printf( "Internal JSONC structure is incomplete.\n" );
        return NULL;
    }
    vNodeMap   = Vec_IntStartFull( pNodes->count );
    vGateIdx   = Vec_IntAlloc( pNodes->count );
    vPoIdx     = Vec_IntAlloc( pNodes->count );
    vPiBases   = Vec_PtrAlloc( pNodes->count );
    vPiBits    = Vec_IntAlloc( pNodes->count );
    vPoBases   = Vec_PtrAlloc( pNodes->count );
    vPoBits    = Vec_IntAlloc( pNodes->count );
    // first pass: collect object types and names
    for ( i = 0; i < (int)pNodes->count; i++ )
    {
        json_value_t Node = pNodes->data.values[i];
        json_value_t * pType = Jsonc_ObjectLookup( pJson, Node, "type" );
        json_value_t * pName = Jsonc_ObjectLookup( pJson, Node, "name" );
        json_value_t * pBit  = Jsonc_ObjectLookup( pJson, Node, "bit" );
        int Bit = 0;
        if ( pType == NULL || pType->type != JSON_STRING )
        {
            printf( "Node %d does not have a valid \"type\" field.\n", i );
            goto cleanup;
        }
        if ( pBit && !Jsonc_ParseInt( pJson, *pBit, &Bit ) )
        {
            printf( "Node %d has an invalid \"bit\" field.\n", i );
            goto cleanup;
        }
        if ( Jsonc_StringEqual( pJson, *pType, "pi" ) )
        {
            Vec_IntWriteEntry( vNodeMap, i, nCis++ );
            pBase = Jsonc_StringDup( pJson, pName ? *pName : *pType );
            if ( pBase == NULL )
            {
                printf( "Primary input %d is missing a name.\n", i );
                goto cleanup;
            }
            Vec_PtrPush( vPiBases, pBase );
            Vec_IntPush( vPiBits, Bit );
        }
        else if ( Jsonc_StringEqual( pJson, *pType, "instance" ) )
        {
            Vec_IntPush( vGateIdx, i );
            nNodes++;
        }
        else if ( Jsonc_StringEqual( pJson, *pType, "PO" ) || Jsonc_StringEqual( pJson, *pType, "po" ) )
        {
            Vec_IntPush( vPoIdx, i );
            nCos++;
            pBase = Jsonc_StringDup( pJson, pName ? *pName : *pType );
            if ( pBase == NULL )
            {
                printf( "Primary output %d is missing a name.\n", i );
                goto cleanup;
            }
            Vec_PtrPush( vPoBases, pBase );
            Vec_IntPush( vPoBits, Bit );
        }
        else
        {
            printf( "Node %d has unsupported type.\n", i );
            goto cleanup;
        }
    }
    // assign IDs to internal nodes
    for ( i = 0; i < Vec_IntSize(vGateIdx); i++ )
        Vec_IntWriteEntry( vNodeMap, Vec_IntEntry(vGateIdx, i), nCis + i );
    // allocate storage for mapping
    vMapping   = Vec_IntAlloc( 4 + nNodes * 4 + nCos + 10 );
    vNames     = Vec_StrAlloc( 1024 );
    vPoDrivers = Vec_IntAlloc( nCos );
    Vec_IntPush( vMapping, nCis );
    Vec_IntPush( vMapping, nCos );
    Vec_IntPush( vMapping, nNodes );
    Vec_IntPush( vMapping, 0 ); // flops
    // second pass: build nodes and POs
    for ( i = 0; i < (int)pNodes->count; i++ )
    {
        json_value_t Node = pNodes->data.values[i];
        json_value_t * pType = Jsonc_ObjectLookup( pJson, Node, "type" );
        if ( Jsonc_StringEqual( pJson, *pType, "instance" ) )
        {
            json_value_t * pGateName = Jsonc_ObjectLookup( pJson, Node, "name" );
            json_value_t * pFanins   = Jsonc_ObjectLookup( pJson, Node, "fanins" );
            json_container_t * pFanObj;
            Mio_Gate_t * pGate;
            Mio_Pin_t * pPin;
            char * pGateStr;
            if ( pGateName == NULL || pGateName->type != JSON_STRING )
            {
                printf( "Gate node %d is missing a name.\n", i );
                goto cleanup;
            }
            pGateStr = Jsonc_StringDup( pJson, *pGateName );
            if ( pGateStr == NULL )
            {
                printf( "Gate node %d has an invalid name.\n", i );
                goto cleanup;
            }
            pGate = Mio_LibraryReadGateByName( pLib, pGateStr, NULL );
            if ( pGate == NULL )
            {
                printf( "Gate \"%s\" is not found in the current library.\n", pGateStr );
                ABC_FREE( pGateStr );
                goto cleanup;
            }
            if ( pFanins == NULL || pFanins->type != JSON_OBJECT )
            {
                printf( "Gate \"%s\" is missing \"fanins\" description.\n", pGateStr );
                ABC_FREE( pGateStr );
                goto cleanup;
            }
            pFanObj = Jsonc_GetContainer( pJson, *pFanins );
            if ( pFanObj == NULL )
            {
                printf( "Gate \"%s\" has incomplete fanin information.\n", pGateStr );
                ABC_FREE( pGateStr );
                goto cleanup;
            }
            Vec_IntPush( vMapping, Mio_GateReadPinNum(pGate) );
            for ( pPin = Mio_GateReadPins(pGate), k = 0; pPin; pPin = Mio_PinReadNext(pPin), k++ )
            {
                json_value_t * pPinInfo = Jsonc_ObjectLookup( pJson, *pFanins, Mio_PinReadName(pPin) );
                json_value_t * pNodeLit;
                int NodeId, MapId;
                if ( pPinInfo == NULL || pPinInfo->type != JSON_OBJECT )
                {
                    printf( "Gate \"%s\" is missing connection for pin \"%s\".\n", pGateStr, Mio_PinReadName(pPin) );
                    ABC_FREE( pGateStr );
                    goto cleanup;
                }
                pNodeLit = Jsonc_ObjectLookup( pJson, *pPinInfo, "node" );
                if ( pNodeLit == NULL || !Jsonc_ParseInt( pJson, *pNodeLit, &NodeId ) )
                {
                    printf( "Gate \"%s\" has invalid node reference on pin \"%s\".\n", pGateStr, Mio_PinReadName(pPin) );
                    ABC_FREE( pGateStr );
                    goto cleanup;
                }
                if ( NodeId < 0 || NodeId >= Vec_IntSize(vNodeMap) )
                {
                    printf( "Gate \"%s\" references out-of-range node %d.\n", pGateStr, NodeId );
                    ABC_FREE( pGateStr );
                    goto cleanup;
                }
                MapId = Vec_IntEntry( vNodeMap, NodeId );
                if ( MapId < 0 )
                {
                    printf( "Gate \"%s\" refers to unsupported node %d.\n", pGateStr, NodeId );
                    ABC_FREE( pGateStr );
                    goto cleanup;
                }
                Vec_IntPush( vMapping, MapId );
            }
            Vec_StrPrintStr( vNames, pGateStr );
            Vec_StrPush( vNames, '\0' );
            ABC_FREE( pGateStr );
        }
        else if ( Jsonc_StringEqual( pJson, *pType, "PO" ) || Jsonc_StringEqual( pJson, *pType, "po" ) )
        {
            json_value_t * pFanin  = Jsonc_ObjectLookup( pJson, Node, "fanin" );
            json_value_t * pNodeId = pFanin ? Jsonc_ObjectLookup( pJson, *pFanin, "node" ) : NULL;
            int NodeId, MapId;
            if ( pNodeId == NULL || !Jsonc_ParseInt( pJson, *pNodeId, &NodeId ) )
            {
                printf( "Primary output %d is missing driver information.\n", Vec_IntSize(vPoDrivers) );
                goto cleanup;
            }
            if ( NodeId < 0 || NodeId >= Vec_IntSize(vNodeMap) )
            {
                printf( "Primary output %d refers to out-of-range node %d.\n", Vec_IntSize(vPoDrivers), NodeId );
                goto cleanup;
            }
            MapId = Vec_IntEntry( vNodeMap, NodeId );
            if ( MapId < 0 )
            {
                printf( "Primary output %d points to unsupported node %d.\n", Vec_IntSize(vPoDrivers), NodeId );
                goto cleanup;
            }
            Vec_IntPush( vPoDrivers, MapId );
        }
    }
    if ( Vec_IntSize(vPoDrivers) != nCos )
    {
        printf( "JSONC file declares %d POs but %d drivers were found.\n", nCos, Vec_IntSize(vPoDrivers) );
        goto cleanup;
    }
    // append CO drivers
    Vec_IntForEachEntry( vPoDrivers, k, i )
        Vec_IntPush( vMapping, k );
    // append gate / CI / CO names
    Jsonc_AppendPortNames( vNames, vPiBases, vPiBits );
    Jsonc_AppendPortNames( vNames, vPoBases, vPoBits );
    // align to 4 bytes and append strings as ints
    {
        int nExtra = (4 - Vec_StrSize(vNames) % 4) % 4;
        int nWords, * pBuffer;
        for ( i = 0; i < nExtra; i++ )
            Vec_StrPush( vNames, '\0' );
        nWords  = Vec_StrSize(vNames) / 4;
        pBuffer = (int *)Vec_StrArray( vNames );
        for ( i = 0; i < nWords; i++ )
            Vec_IntPush( vMapping, pBuffer[i] );
    }
    fSuccess = 1;
cleanup:
    if ( fSuccess == 0 && ppDesignName && *ppDesignName )
        ABC_FREE( *ppDesignName );
    Vec_IntFreeP( &vPoDrivers );
    Vec_IntFreeP( &vNodeMap );
    Vec_IntFreeP( &vGateIdx );
    Vec_IntFreeP( &vPoIdx );
    Vec_IntFreeP( &vPiBits );
    Vec_IntFreeP( &vPoBits );
    if ( vNames )
        Vec_StrFree( vNames );
    if ( vPiBases )
    {
        Vec_PtrForEachEntry( char *, vPiBases, pBase, i )
            ABC_FREE( pBase );
        Vec_PtrFree( vPiBases );
    }
    if ( vPoBases )
    {
        Vec_PtrForEachEntry( char *, vPoBases, pBase, i )
            ABC_FREE( pBase );
        Vec_PtrFree( vPoBases );
    }
    if ( fSuccess == 0 && vMapping )
    {
        Vec_IntFree( vMapping );
        vMapping = NULL;
    }
    return vMapping;
}
Abc_Ntk_t * Jsonc_ReadNetwork( char * pFileName )
{
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen();
    Vec_Int_t * vMapping;
    Abc_Ntk_t * pNtk;
    char * pDesignName = NULL;
    json_t * pJson = json_create();
    if ( pJson == NULL )
    {
        printf( "Failed to allocate JSONC parser.\n" );
        return NULL;
    }
    if ( !json_load_file( pJson, pFileName ) )
    {
        printf( "Failed to load JSONC file \"%s\".\n", pFileName );
        json_destroy( pJson );
        return NULL;
    }
    vMapping = Jsonc_ConvertToMiniMapping( pJson, pLib, &pDesignName );
    json_destroy( pJson );
    if ( vMapping == NULL )
        return NULL;
    pNtk = Abc_NtkFromMiniMapping( Vec_IntArray(vMapping) );
    Vec_IntFree( vMapping );
    if ( pNtk == NULL )
    {
        ABC_FREE( pDesignName );
        return NULL;
    }
    ABC_FREE( pNtk->pName );
    pNtk->pName = pDesignName ? pDesignName : Extra_FileNameGeneric( pFileName );
    ABC_FREE( pNtk->pSpec );
    pNtk->pSpec = Abc_UtilStrsav( pFileName );
    return pNtk;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
