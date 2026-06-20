/*
 * mtlx_xml.h - tiny dependency-free XML parser (subset sufficient for .mtlx).
 *
 * Handles elements, attributes, self-closing tags, comments, the <?xml?> and
 * <!DOCTYPE> prologue, and the five predefined entities in attribute values.
 * Text content between tags is ignored (MaterialX carries data in attributes).
 */
#ifndef MTLXRENDER_MTLX_XML_H_
#define MTLXRENDER_MTLX_XML_H_

typedef struct { char *name; char *value; } XmlAttr;

typedef struct XmlNode {
    char *tag;
    XmlAttr *attrs;
    int nattr;
    struct XmlNode *children;
    int nchild;
} XmlNode;

/* Parse a file. Returns a synthetic root whose children are the document's
 * top-level elements, or NULL on error. Free with xml_free(). */
XmlNode *xml_parse_file(const char *path);
void xml_free(XmlNode *root);

/* Attribute lookup by name; NULL if absent. */
const char *xml_attr(const XmlNode *n, const char *name);

/* First direct child whose tag equals `tag`; NULL if none. */
const XmlNode *xml_child(const XmlNode *n, const char *tag);

#endif /* MTLXRENDER_MTLX_XML_H_ */
