// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: List class with storage in existing classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LIST_H_
#define VERILATOR_V3LIST_H_

#include "config_build.h"
#include "verilatedos.h"

#include <type_traits>
#include <utility>

//============================================================================

template <class T>
class V3List;
template <class T>
class V3ListEnt;

template <class T>
class V3List final {
    // List container for linked list of elements of type *T  (T is a pointer type)
private:
    // MEMBERS
    T m_headp = nullptr;  // First element
    T m_tailp = nullptr;  // Last element
    friend class V3ListEnt<T>;

public:
    V3List() = default;
    ~V3List() = default;
    // METHODS
    T begin() const { return m_headp; }
    T end() const { return nullptr; }
    T rbegin() const { return m_tailp; }
    T rend() const { return nullptr; }
    bool empty() const { return m_headp == nullptr; }
    void reset() {  // clear() without walking the list
        m_headp = nullptr;
        m_tailp = nullptr;
    }
};

//============================================================================

template <class T>
class V3ListEnt final {
    // List entry for linked list of elements of type *T  (T is a pointer type)
private:
    // MEMBERS
    T m_nextp = nullptr;  // Pointer to next element, nullptr=end
    T m_prevp = nullptr;  // Pointer to previous element, nullptr=beginning
    friend class V3List<T>;
    static V3ListEnt* baseToListEnt(void* newbasep, size_t offset) {
        // "this" must be an element inside of *basep
        // Use that to determine a structure offset, then apply to the new base
        // to get our new pointer information
        return (V3ListEnt*)(((uint8_t*)newbasep) + offset);
    }

public:
    V3ListEnt() = default;
    ~V3ListEnt() {
#ifdef VL_DEBUG
        // Load bogus pointers so we can catch deletion bugs
        m_nextp = reinterpret_cast<T>(1);
        m_prevp = reinterpret_cast<T>(1);
#endif
    }
    T nextp() const { return m_nextp; }
    T prevp() const { return m_prevp; }
    // METHODS
    void pushBack(V3List<T>& listr, T newp) {
        // "this" must be an element inside of *newp
        // cppcheck-suppress thisSubtraction
        const size_t offset = (size_t)(uint8_t*)(this) - (size_t)(uint8_t*)(newp);
        m_nextp = nullptr;
        if (!listr.m_headp) listr.m_headp = newp;
        m_prevp = listr.m_tailp;
        if (m_prevp) baseToListEnt(m_prevp, offset)->m_nextp = newp;
        listr.m_tailp = newp;
    }
    void pushFront(V3List<T>& listr, T newp) {
        // "this" must be an element inside of *newp
        // cppcheck-suppress thisSubtraction
        const size_t offset = (size_t)(uint8_t*)(this) - (size_t)(uint8_t*)(newp);
        m_nextp = listr.m_headp;
        if (m_nextp) baseToListEnt(m_nextp, offset)->m_prevp = newp;
        listr.m_headp = newp;
        m_prevp = nullptr;
        if (!listr.m_tailp) listr.m_tailp = newp;
    }
    // Unlink from side
    void unlink(V3List<T>& listr, T oldp) {
        // "this" must be an element inside of *oldp
        // cppcheck-suppress thisSubtraction
        const size_t offset = (size_t)(uint8_t*)(this) - (size_t)(uint8_t*)(oldp);
        if (m_nextp) {
            baseToListEnt(m_nextp, offset)->m_prevp = m_prevp;
        } else {
            listr.m_tailp = m_prevp;
        }
        if (m_prevp) {
            baseToListEnt(m_prevp, offset)->m_nextp = m_nextp;
        } else {
            listr.m_headp = m_nextp;
        }
        m_prevp = m_nextp = nullptr;
    }
    // Remove all nodes from 'oldListr', append them to 'newListr'. 'this' must be a member of the
    // object at 'selfp', and 'selfp' must be the head of the list in 'oldListr'.
    void moveAppend(V3List<T>& oldListr, V3List<T>& newListr, T selfp) {
        UASSERT(selfp == oldListr.m_headp, "Must be head of list to use 'moveAppend'");
        const size_t offset = (size_t)(uint8_t*)(this) - (size_t)(uint8_t*)(selfp);
        const T headp = selfp;
        const T tailp = oldListr.m_tailp;
        oldListr.reset();
        if (newListr.empty()) {
            newListr.m_headp = headp;
            newListr.m_tailp = tailp;
        } else {
            baseToListEnt(newListr.m_tailp, offset)->m_nextp = headp;
            m_prevp = newListr.m_tailp;
            newListr.m_tailp = tailp;
        }
    }
};

//============================================================================

// The list links, to be added as a member to 'Element'. They are considered mutable, even in a
// 'const Element', as they are only used for storing 'Element' in a collection.
template <typename Base>
class V3List2Links final {
    // The List itself, but nothing else can access the link pointers
    template <typename B, V3List2Links<B> B::*P, typename>
    friend class V3List2;

    Base* m_nextp = nullptr;  // Next element in list
    Base* m_prevp = nullptr;  // Previous element in list

public:
    V3List2Links() = default;
    ~V3List2Links() {
#ifdef VL_DEBUG
        m_nextp = reinterpret_cast<Base*>(1);
        m_prevp = reinterpret_cast<Base*>(1);
#endif
    }
    VL_UNCOPYABLE(V3List2Links);
    VL_UNMOVABLE(V3List2Links);
};

template <typename Base, V3List2Links<Base> Base::*LinksPointer, typename Element = Base>
class V3List2 final {
    static_assert(std::is_base_of<Base, Element>::value, "'Element' must be a subtype of 'Base");
    Base* m_headp = nullptr;
    Base* m_tailp = nullptr;

    // Given the Element, return the Links. The links are always mutable, even in const elements.
    VL_ATTR_ALWINLINE
    static V3List2Links<Base>& toLinks(const Base& element) {
        return const_cast<Base&>(element).*LinksPointer;
    }

    // Bare-bones iterator class for List. This is just enough to support range based for loops and
    // basic usage. Feel free to extend as required.
    template <typename IteratorElement>
    class Iterator final {
        static_assert(std::is_same<IteratorElement, Element>::value
                          || std::is_same<IteratorElement, const Element>::value,
                      "'Iterator' must be used with element type only");

        // The List itself, but nothing else can construct iterators
        template <typename B, V3List2Links<B> B::*P, typename>
        friend class V3List2;

        using SelfType = Iterator<IteratorElement>;

        Base* m_currp;  // Currently iterated element, or 'nullptr' for 'end()'

        Iterator(Base* elementp)
            : m_currp{elementp} {
            VL_PREFETCH_RW(elementp);
        }
        Iterator(std::nullptr_t)
            : m_currp{nullptr} {}

    public:
        // Dereference
        IteratorElement& operator*() const {
            UASSERT(m_currp, "Dereferencing end of list iterator");
            return *static_cast<IteratorElement*>(m_currp);
        }
        // Pre increment
        SelfType& operator++() {
            UASSERT(m_currp, "Pre-incrementing end of list iterator");
            m_currp = toLinks(*m_currp).m_nextp;
            if (VL_LIKELY(m_currp)) VL_PREFETCH_RW(m_currp);
            return *this;
        }
        // Post increment
        SelfType operator++(int) {
            UASSERT(m_currp, "Post-incrementing end of list iterator");
            Base* const elementp = m_currp;
            m_currp = toLinks(*elementp).m_nextp;
            if (VL_LIKELY(m_currp)) VL_PREFETCH_RW(m_currp);
            return SelfType{elementp};
        }
        // Equals
        bool operator==(const SelfType& other) const { return m_currp == other.m_currp; }
        // Not equals
        bool operator!=(const SelfType& other) const { return m_currp != other.m_currp; }
        // Convert to const iterator
        operator Iterator<const IteratorElement>() const {
            return Iterator<const IteratorElement>{m_currp};
        }
    };

public:
    using List = V3List2<Base, LinksPointer, Element>;
    using iterator = Iterator<Element>;
    using const_iterator = Iterator<const Element>;

    V3List2() = default;
    ~V3List2() {
#ifdef VL_DEBUG
        m_headp = reinterpret_cast<Element*>(1);
        m_tailp = reinterpret_cast<Element*>(1);
#endif
    }
    VL_UNCOPYABLE(V3List2);
    VL_UNMOVABLE(V3List2);

    bool empty() const {
        UASSERT(!m_headp == !m_tailp, "Inconsistent list");
        return !m_headp;
    }
    Element& front() { return *static_cast<Element*>(m_headp); }
    const Element& front() const { return *static_cast<Element*>(m_headp); }
    Element& back() { return *static_cast<Element*>(m_tailp); }
    const Element& back() const { return *static_cast<Element*>(m_tailp); }

    iterator begin() { return iterator{m_headp}; }
    const_iterator begin() const { return const_iterator{m_headp}; }
    iterator end() { return iterator{nullptr}; }
    const_iterator end() const { return const_iterator{nullptr}; }

    void push_back(const Element& element) {
        auto& links = toLinks(element);
        links.m_nextp = nullptr;
        links.m_prevp = m_tailp;
        if (m_tailp) toLinks(*m_tailp).m_nextp = &const_cast<Element&>(element);
        m_tailp = &const_cast<Element&>(element);
        if (!m_headp) m_headp = m_tailp;
    }

    void pop_back() {
        UASSERT(!empty(), "'pop_back' called on empty list");
        m_tailp = toLinks(*m_tailp).m_prevp;
        if (m_tailp) {
            toLinks(*m_tailp).m_nextp = nullptr;
        } else {
            m_headp = nullptr;
        }
    }

    void push_front(const Element& element) {
        auto& links = toLinks(element);
        links.m_nextp = m_headp;
        links.m_prevp = nullptr;
        if (m_headp) toLinks(*m_headp).m_prevp = &const_cast<Element&>(element);
        m_headp = &const_cast<Element&>(element);
        if (!m_tailp) m_tailp = m_headp;
    }

    void pop_front() {
        UASSERT(!empty(), "'pop_front' called on empty list");
        m_headp = static_cast<Element*>(toLinks(*m_headp).m_nextp);
        if (m_headp) {
            toLinks(*m_headp).m_prevp = nullptr;
        } else {
            m_tailp = nullptr;
        }
    }

    void erase(const Element& element) {
        auto& links = toLinks(element);
        if (links.m_nextp) toLinks(*links.m_nextp).m_prevp = links.m_prevp;
        if (links.m_prevp) toLinks(*links.m_prevp).m_nextp = links.m_nextp;
        if (m_headp == &element) m_headp = links.m_nextp;
        if (m_tailp == &element) m_tailp = links.m_prevp;
        links.m_prevp = nullptr;
        links.m_nextp = nullptr;
    }

    void swap(List& other) {
        std::swap(m_headp, other.m_headp);
        std::swap(m_tailp, other.m_tailp);
    }

    void splice(const_iterator pos, List& other) {
        if (empty()) {
            swap(other);
        } else if (other.empty()) {
            return;
        } else {
            UASSERT(pos == end(), "Sorry, only splicing at the end is implemented at the moment");
            toLinks(*m_tailp).m_nextp = other.m_headp;
            toLinks(*other.m_headp).m_prevp = m_tailp;
            m_tailp = other.m_tailp;
            other.m_headp = nullptr;
            other.m_tailp = nullptr;
        }
    }
};

#endif  // Guard
